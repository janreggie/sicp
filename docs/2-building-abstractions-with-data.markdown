# Building Abstractions with Data

## 2.1 Introduction to Data Abstraction

### Exercise 2.1

```scheme
(define (make-rat n d)
  (if (< d 0)
    (make-rat (- n) (- d))
    (let ((g (abs (gcd n d))))
      (cons (/ n g) (/ d g)))))
```

Ensure that `d` is always positive, and make `g` always positive.

### Exercise 2.2

```scheme
; make-point creates a pair of x-y coordinates
(define (make-point x y) (cons x y))

; x-point and y-point return the x and y coordinates of a point p
(define (x-point p) (car p))
(define (y-point p) (cdr p))

; print-point prints details about a point
(define (print-point p)
  (newline)
  (display "(")
  (display (x-point p))
  (display ",")
  (display (y-point p))
  (display ")"))

; make-segment creates a segment of two points
(define (make-segment p1 p2) (cons p1 p2))

; start-segment returns the first point of a segment
(define (start-segment s) (car s))

; end-segment returns the second point of a segment
(define (end-segment s) (cdr s))

(define ss (make-segment (make-point 1 2) (make-point 3 4)))
(print-point (start-segment ss)) ; ==> (1,2)
(print-point (end-segment ss)) ; ==> (3,4)
```

### Exercise 2.3

```scheme
; make-rectangle creates a rectangle with c1, c2 as corners.
; Note that c1 and c2 can be anywhere in the plane,
; but the rectangle's segments will remain parallel to the x- and y-axes.
; For instance, c1=(1,4), c2=(4,2) creates a 3x2 rectangle.
(define (make-rectangle c1 c2) (cons c1 c2))

; width returns the width of the rectangle
(define (width r)
  (abs (- (x-point (car r)) (x-point (cdr r)))))

; height returns the height of the rectangle
(define (height r)
  (abs (- (y-point (car r)) (y-point (cdr r)))))

; perimeter computes for the perimeter of the rectangle.
; If the rectangle has zero width or height, it will return zero.
(define (perimeter r)
  (if (or (= (width r) 0) (= (height r) 0))
    0
    (* 2 (+ (width r) (height r)))))

; area returns the area of the rectangle.
(define (area r)
  (* (width r) (height r)))
```

All these functions can be tested as follows:

```scheme
(define rect
  (make-rectangle
    (make-point 1 4)
    (make-point 5 1)))
(perimeter rect) ; ==> 14
(area rect) ; ==> 12
```

### Exercise 2.4

```scheme
(define (cons x y)
  (lambda (m) (m x y)))
```

The procedure `cons` takes in two parameters `x` and `y` and returns a procedure that takes in a callable object `m` and returns the value `(m x y)`.

```scheme
(define (car z)
  (z (lambda (p q) p)))
```

The procedure `car` takes in a callable object `z`, which in turn takes in a function that takes two callable values `p` and `q`, and then return `q`.

This is actually a very clever way of "implementing" `cons` and `car`. The following is what goes on:

```scheme
(define pt (cons 2 3))  ; pt = (lambda (m) (m 2 3))
(car pt)
; (pt (lambda (p q) p))
; ((lambda (m) (m 2 3)) (lambda (p q) p))
; ((lambda (p q) p) 2 3)
; 2
```

Now, let us try constructing a `cdr` using the example for `car`.

```scheme
(define (cdr z)
  (z (lambda (p q) q)))
(cdr pt)
; (pt (lambda (p q) q))
; ((lambda (m) (m 2 3)) (lambda (p q) q))
; ((lambda (p q) q) 2 3)
; 3
```

### Exercise 2.5

This implementation requires repeatedly dividing the result by 2 or 3 to check how many 2's or 3's the value has.

```scheme
(define (cons x y)
  (* (expt 2 x) (expt 3 y)))

(define (car p)
  (define (iter val res)
    (if (= (remainder val 2) 0)
      (iter (/ val 2) (+ res 1))
      res))
  (iter p 0))

(define (cdr p)
  (define (iter val res)
    (if (= (remainder val 3) 0)
      (iter (/ val 3) (+ res 1))
      res))
  (iter p 0))

(define pt (cons 3 4))
(car pt) ; ==> 3
(cdr pt) ; ==> 4
```

### Exercise 2.6

```scheme
(define zero (lambda (f) (lambda (x) x)))
```

This defines `zero` as a function that takes in a function `f` and returns... a function that takes in `x` and returns the same `x`.

```scheme
(define (add-1 n)
  (lambda (f) (lambda (x) (f ((n f) x)))))
```

This defines `add-1` as a procedure that takes in a callable value `n` and returns a function that takes in `f` that returns a function that takes in `x` and returns `(f ((n f) x))`. Now that *is* mind-boggling...

Let us try solving for `(add-1 zero)`:

```scheme
(add-1 zero)
; (add-1 (lambda (f) (lambda (x) x)))
; (lambda (f) (lambda (x) (f (((lambda (f) (lambda (x) x)) f) x))))
; (lambda (f) (lambda (x) (f ((lambda (x) x) x))))
; (lambda (f) (lambda (x) (f x)))
```

Notice what happened here: `(add-1 zero)` takes in a function `f` and returns a function that takes in `x` and returns `(f x)`.

Let us try to do that again.

```scheme
(add-1 (add-1 zero))
; (add-1 (lambda (f) (lambda (x) (f x))))
; (lambda (f) (lambda (x) (f (((lambda (f) (lambda (x) (f x))) f) x))))
; (lambda (f) (lambda (x) (f ((lambda (x) (f x)) x))))
; (lambda (f) (lambda (x) (f (f x))))
```

Another `add-1` adds a call to `f`.

Since `(add-1 zero)` is just `one` and `(add-1 one)` is `two`, we can easily give direct definitions for them:

```scheme
(define one (lambda (f) (lambda (x) (f x))))
(define two (lambda (f) (lambda (x) (f (f x)))))
```

We can also make a `+` procedure which takes in two "Church numerals" and return their sum. But how do we do this is another thing...

Suppose `a` is a Church numeral that represents the number `A` in Church encoding, i.e., `(lambda (f) (lambda (x) (f (f ... (f x))))))` where `f` is callled `A` times. Similarly, let `b` be a Church numeral that represents `B` in Church encoding.

Note `(a f)` and `(b f)` become `(lambda (x) (f (f ... (f x))))` where `f` is composed `A` and `B` times respectively. We would want to get a result such that the number of calls for `f` is `A+B`. Simple: `((a f) ((b f) x))`. `((b f) x)` returns `(f (f ... (f x)))` repeated `B` times, and that is wrapped around `(a f)` which calls `f` `A` times!

```scheme
(define (+ a b)
  (lambda (f)
    (lambda (x)
      ((a f) ((b f) x)))))
```
