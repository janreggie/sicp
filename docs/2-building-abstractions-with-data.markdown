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

### Exercise 2.7

The implementation of `make-interval` does not mandate `a` be less than `b` or vice versa. A check might be needed.

```scheme
(define (lower-bound x) (min (car x) (cdr x)))
(define (upper-bound x) (max (car x) (cdr x)))
```

### Exercise 2.8

The difference between the two ranges is the range between the smallest possible difference to the largest possible one. The smallest possible difference can be taken by minimizing the first number and maximizing the second, while the largest possible one can be taken by maximizing the second number and minimizing the first.

Suppose that the first range is 5 to 8 and the second 1 to 2. The smallest possible difference is $5-2=3$ while the largest one is $8-1=7$. Implementing it should be easy.

```scheme
; sub-interval determines the interval for the difference between x and y
(define (sub-interval x y)
  (make-interval
    (- (lower-bound x) (upper-bound y))
    (- (upper-bound x) (lower-bound y))))
(define a (make-interval 5 8))
(define b (make-interval 1 2))
(sub-interval a b) ; 3 - 7
```

### Exercise 2.9

Suppose $x=\left[a,b\right]$ and $y=\left[c,d\right]$, and $W\left(x\right)$ be the width function for $x$. Hence, $W\left(x\right)=\frac{b-a}{2}$ and $W\left(y\right)=\frac{d-c}{2}$.

We see that $x+y=[a+c,b+d]$ and $x-y=[a-d,b-c]$. Astonishingly, $W\left(x+y\right)=W\left(x-y\right)=\frac{\left(b+d\right)-\left(a+c\right)}{2}$, which subsequently equals $W\left(x\right)+W\left(y\right)$.

For multiplication, $x\times y = \left[\max\left(ac,ad,bc,bd\right), \min\left(ac,ad,bc,bd\right)\right]$, and so $W\left(x\times y\right)$ can become uncertain, hence there is no direct relationship between that and either of $W\left(x\right)$ and $W\left(y\right)$. This goes the same with division, which is dependent on multiplication.

### Exercise 2.10

```scheme
(define (div-interval x y)
  ; spans-zero returns true if x spans zero by checking its signs
  (define (spans-zero x)
    (< (* (lower-bound x) (upper-bound x)) 0))
  (if (spans-zero y)
    (error "Dividend spans zero")
    (mul-interval x
      (make-interval
        (/ 1.0 (upper-bound y))
        (/ 1.0 (lower-bound y))))))
(div-interval
  (make-interval 1 5)
  (make-interval 2 3)) ; returns something alright
(div-interval
  (make-interval 1 5)
  (make-interval -2 3)) ; returns an error
```

### Exercise 2.11

Suppose $S\left(x\right)$ has the following property:

$$
S\left(\left[a,b\right]\right) = \left\{\begin{array}{lr}
    -1 & \text{if } a \lt 0 \text{ and } b \lt 0\\
    0  & \text{if } a \lt 0 \text{ and } b \ge 0\\
    1  & \text{if } a \ge 0 \text{ and } b \ge 0
    \end{array}\right.
$$

With $x=\left[a,b\right]$ and $y=\left[c,d\right]$, there are nine possible combinations for $x\times y$ determined by their $S$-values:

$$
% painstakingly transcribed using https://isaurssaurav.github.io/mathjax-table-generator/
\begin{array} {|r|r|}\hline _{S(x)} \backslash ^{S(y)} & -1 & 0 & 1 \\ \hline -1 & \left[bd,ac\right] & \left[ad,ac\right] & \left[ad,bc\right] \\ \hline 0 & \left[bc,ac\right] & \star & \left[ad,bd\right] \\ \hline 1 & \left[bc,ad\right] & \left[bc,bd\right] & \left[ac,bd\right] \\ \hline  \end{array}
$$

These ranges have been computed by hand. Consider when $S\left(x\right)=1$ and $S\left(y\right)=0$. In this case, the smallest possible number could be taken from $b$, the larger positive number in the range $x$, multiplied to $c$, the smallest negative number in $y$. Similarly, the largest possible number in the product could be taken from $b$ multiplied to $d$, the largest positive number in $y$. (Try using the example $x=\left[1,4\right]$ and $y=\left[-2,3\right]$.)

The middle case, when both $x$ and $y$ span zero, is a bit stranger. The negative extrema $bc$ and $ad$, and the positive extrema $ac$ and $bd$, can be smaller or larger than the other. One has to perform the multiplication operations manually and check the largest value from there.

The following is an implementation:

```scheme
; mul-interval is an implementation of multiplying two intervals
; which uses two multiplication operations most of the time
(define (mul-interval x y)
  ; neg be less than zero and nonneg be its complement
  (define (neg n) (< n 0))
  (define (nonneg n) (>= n 0))

  ; s be the s-value of a range
  (define (s x)
    (cond
      ((and (neg (lower-bound x)) (neg (upper-bound x))) -1)
      ((and (neg (lower-bound x)) (nonneg (upper-bound x))) 0)
      (else 1)))

  ; now for the great conditional
  (let ((a (lower-bound x))
      (b (upper-bound x))
      (c (lower-bound y))
      (d (upper-bound y))
      (sx (s x))
      (sy (s y)))
    (cond
      ((and (= sx -1) (= sy -1)) (make-interval (* b d) (* a c)))
      ((and (= sx -1) (= sy 0))  (make-interval (* a d) (* a c)))
      ((and (= sx -1) (= sy 1))  (make-interval (* a d) (* b c)))
      ((and (= sx 0)  (= sy -1)) (make-interval (* b c) (* a c)))
      ; skipping sx=0 and sy=0 and putting that as the else statement
      ((and (= sx 0)  (= sy 1))  (make-interval (* a d) (* b d)))
      ((and (= sx 1)  (= sy -1)) (make-interval (* b c) (* a d)))
      ((and (= sx 1)  (= sy 0))  (make-interval (* b c) (* b d)))
      ((and (= sx 1)  (= sy 1))  (make-interval (* a c) (* b d)))
      (else
        (let ((ac (* a c))
            (ad (* a d))
            (bc (* b c))
            (bd (* b d)))
          (make-interval (min ad bc) (max ac bd)))))))
```

Tests can be done by writing two intervals, multiplying them using this and the original implementation, and checking if they are equal.

How much readability one is willing to trade off for performance is dependent on the one who writes the code.

### Exercise 2.12

With some center $c$ and a percent tolerance $p<1$, the range should be $\left[c\left(1-p\right), c\left(1+p\right)\right]$.

```scheme
; make-center-percent makes an interval with center c and percent tolerance p.
; For example, if c=6.8 and p=10, the interval is between 6.8-(6.8*10%) and 6.8+(6.8*10%),
; which is 6.12 and 7.48.
(define (make-center-percent c p)
  (make-interval
    (* c (- 1.0 (/ p 100.0)))
    (* c (+ 1.0 (/ p 100.0)))))
(make-center-percent 6.8 10) ; 6.12 - 7.48
```

### Exercise 2.13

Suppose there are two ranges: the first one having a center of $c_1$ and percentage tolerance $p_1$, and the second having $c_2$ and $p_2$. Henceforth, the two ranges are $\left[{c_1}\left(1-{p_1}\right), {c_1}\left(1+{p_1}\right)\right]$ and $\left[{c_2}\left(1-{p_2}\right), {c_2}\left(1+{p_2}\right)\right]$.

With the assumption that all numbers are positive, the product should have the range $\left[{c_1}{c_2}\left(1-{p_1}\right)\left(1-{p_2}\right), {c_1}{c_2}\left(1+{p_1}\right)\left(1+{p_2}\right)\right]$, which can be written as $\left[{c_1}{c_2}\left(1-\left({p_1}+{p_2}\right)+{p_1}{p_2}\right), {c_1}{c_2}\left(1+\left({p_1}+{p_2}\right)+{p_1}{p_2}\right)\right]$.

If $p_1$ and $p_2$ are *sufficiently* small, ${p_1}{p_2}$ can be negligible, and the range is written as $\left[{c_1}{c_2}\left(1-\left({p_1}+{p_2}\right)\right), {c_1}{c_2}\left(1+\left({p_1}+{p_2}\right)\right)\right]$, which is a range with center ${c_1}{c_2}$ and percentage tolerance ${p_1}+{p_2}$.

### Exercise 2.14

Using a simple test, we see that the two procedures do output different values:

```scheme
(define r1 (make-center-percent 6800 10))
(define r2 (make-center-percent 3000 25))
(par1 r1 r2) ; (1226.179875333927 . 3351.2544802867387)
(par2 r1 r2) ; (1645.1612903225807 . 2497.773820124666)
```

Suppose $x=\left[a,b\right]$ and $y=\left[c,d\right]$. We see that $x+y=\left[a+c,b+d\right]$ and $x\times y=\left[ac, bd\right]$. Let us consider, however, what `div-interval` does:

```scheme
(define (div-interval x y)
  (mul-interval x
    (make-interval
      (/ 1.0 (upper-bound y))
      (/ 1.0 (lower-bound y)))))
```

Or, in mathematical terms:

$$
\begin{aligned}
\left[a,b\right]\div\left[c,d\right] &= \left[a,b\right]\times \left[\frac{1}{d}, \frac{1}{c}\right] \\
  &= \left[\frac{a}{d}, \frac{b}{c}\right]
\end{aligned}
$$

Interestingly, if we have a range $[a,b]$ divided by itself:

$$
\begin{aligned}
\left[a,b\right]\div\left[a,b\right] &= \left[\frac{a}{b}, \frac{b}{a}\right]
\end{aligned}
$$

The current system does not have an identity principle. More on this later.

From here, we can analyze the behaviors of `par1` and `par2`:

$$
\begin{aligned}
\text{par1}\left(x,y\right) &= \left(x\times y\right) \div \left(x+y\right) \\
  &= \left[ac, bd\right] \div \left[a+c, b+d\right] \\
  &= \left[\frac{ac}{b+d}, \frac{bd}{a+c}\right]
\end{aligned}
$$

$$
\begin{aligned}
\text{par2}\left(x,y\right) &= \left[1, 1\right] \div \left(\left(\left[1,1\right] \div x\right) + \left(\left[1,1\right] \div y\right)\right) \\
  &= \left[1,1\right] \div \left(\left(\left[1,1\right] \div \left[a,b\right]\right) + \left(\left[1,1\right] \div \left[c,d\right]\right)\right) \\
  &= \left[1,1\right] \div \left(\left[\frac{1}{b}, \frac{1}{a}\right] + \left[\frac{1}{d}, \frac{1}{c}\right]\right) \\
  &= \left[1,1\right] \div \left(\left[\frac{1}{b} + \frac{1}{d}, \frac{1}{a} + \frac{1}{c}\right]\right) \\
  &= \left[\frac{1}{\frac{1}{a} + \frac{1}{c}} , \frac{1}{\frac{1}{b} + \frac{1}{d}} \right] \\
  &= \left[\frac{ac}{a+c} , \frac{bd}{b+d} \right]
\end{aligned}
$$

### Exercise 2.15

Let us consider the results of the previous exercise. We have to remember that $a<b$ and $c<d$. Therefore, $a+c < b+d$, and this implies that $\left[\frac{ac}{b+d}, \frac{bd}{a+c}\right]$ has a *wider* range than $\left[\frac{ac}{a+c} , \frac{bd}{b+d} \right]$ because of the denominators of the parameters of the former.

While it may be computationally cheaper to compute for ${x}\times{y}$ in `par1`, this will introduce a much larger range than `par2`. This is perhaps the "uncertainty" that Eva Lu Ator is describing.

### Exercise 2.16

Consider the lack of identity in `div-interval`. Because of this, $x + y \div y \neq x$. The two expressions should be equivalent, but they aren't. A principle of "identity" should be established where a program knows if an operation is applied to two "same" intervals, although doing so is a lot harder than it looks, and I can't say if it even were possible.

## 2.2 Hierarchial Data and the Closure Property

### Exercise 2.17

```scheme
; last-pair returns a pair which only contains the last element of a given list
(define (last-pair items)
  (if (null? (cdr items))
    items
    (last-pair (cdr items))))
(last-pair (list 23 72 149 34)) ; (34)
```

### Exercise 2.18

Note that `(cdr items)` returns either a list or nil, and `(car items)` returns a single number. From here, how are we able to reverse a list? Of course, without using the built-in `reverse`.

Remember that `last-pair` takes in the last "pair" of the list (its `cdr` is an empty value, so really it's a pair with only one element). This can be a very useful procedure.

A `reverse` procedure would use `last-pair` to get the very last item, and a `all-but-last` procedure which returns the entire list without the very last element.

```scheme
(define (all-but-last items)
  (if (null? (cdr items))
    ()
    (cons (car items) (all-but-last (cdr items)))))
(all-but-last (list 23 72 149 34)) ; (23 72 149)

(define (reverse items)
  (if (null? items)
    items
    (cons (car (last-pair items)) (reverse (all-but-last items)))))
(reverse (list 23 72 149 34)) ; (34 149 72 23)
```

### Exercise 2.19

```scheme
; first-denomination returns the first item on items
(define (first-denomination items)
  (car items))

; except-first-denomination returns items but the first one
(define (except-first-denomination items)
  (cdr items))

; no-more? checks if items is empty
(define (no-more? items)
  (null? items))

; using the previous procedures, as well as those in the book
(cc 100 us-coins) ; 292
```

On whether order matters for `coin-values`, after every iteration, `cc` branches between when `first-denomination` has been chosen, and when it isn't and `first-denomination` is no longer available as an option. The order of the coins should not matter, since all permutations will be attempted.

A simple demonstration of this, although definitely not solid proof, can be seen if `us-coins` were reversed:

```scheme
(cc 100 (reverse us-coins)) ; also 292
```

### Exercise 2.20

```scheme
(define (same-parity . items)
  (define (is-same-parity? x) (= (remainder (car items) 2) (remainder x 2)))
  (filter is-same-parity? items))
(same-parity 1 2 3 4 5 6 7) ; (1 3 5 7)
(same-parity 2 3 4 5 6 7) ; (2 4 6)
```

Wait, we aren't allowed to use `filter` yet? Okay then.

```scheme
(define (same-parity . items)
  (define (is-same-parity? x) (= (remainder (car items) 2) (remainder x 2)))

  ; recurse recurses through items with is-same-parity? and returns accum
  (define (recurse items accum)
    (cond
      ((null? items) accum)
      ((is-same-parity? (car items)) (recurse (cdr items) (cons (car items) accum)))
      (else (recurse (cdr items) accum))))

  ; one call to reverse since accum appends to the left every time
  (reverse (recurse items ())))
(same-parity 1 2 3 4 5 6 7) ; (1 3 5 7)
(same-parity 2 3 4 5 6 7) ; (2 4 6)
```

### Exercise 2.21

```scheme
(define (square-list items)
  (if (null? items)
    () ; "nil"
    (cons (square (car items)) (square-list (cdr items)))))
(square-list (list 1 2 3 4))

(define (square-list items)
  (map square items))
(square-list (list 1 2 3 4))
```

### Exercise 2.22

```scheme
(define (square-list items)
  (define (iter things answer)
    (if (null? things)
      answer
      (iter (cdr things)
        (cons (square (car things))
          answer))))
  (iter items ()))
(square-list (list 1 2 3 4))
; (iter (list 1 2 3 4) ())
; (iter (list 2 3 4) (cons (square 1) ()))
; (iter (list 2 3 4) (list 1))
; (iter (list 3 4) (cons (square 2) (list 1)))
; (iter (list 3 4) (list 4 1))
; (iter (list 4) (cons (square 3) (list 4 1)))
; (iter (list 4) (list 9 4 1))
; (iter () (cons (square 4) (list 9 4 1)))
; (iter () (list 16 9 4 1))
; (list 16 9 4 1)
```

For every subsequent value taken from `things`, it is appended at the start of `answer`. The answers are stacked FILO.

```scheme
(define (square-list items)
  (define (iter things answer)
    (if (null? things)
      answer
      (iter (cdr things)
        (cons answer
          (square (car things))))))
  (iter items ()))
(square-list (list 1 2 3 4))
; (iter (list 1 2 3 4) ())
; (iter (list 2 3 4) (cons () (square 1)))
; (iter (list 2 3 4) (list () 1))
; (iter (list 3 4) (cons (list () 1) (square 2)))
; (iter (list 3 4) (list (list () 1) 4))
; (iter (list 4) (cons (list (list () 1) 4) (square 3)))
; (iter (list 4) (list (list (list () 1) 4) 9))
; (iter () (cons (list (list (list () 1) 4) 9) (square 4)))
; (iter () (list (list (list (list () 1) 4) 9) 16))
; (list (list (list (list () 1) 4) 9) 16)
```

The problem here is that a list is `cons`'d to a value, which should be the other way around. The final pair has a *list* in its first half, and a single *value* at its second. This will yield MIT Scheme to display something weird:

```text
1 ]=> (square-list (list 1 2 3 4))
;Value: ((((() . 1) . 4) . 9) . 16)
```

### Exercise 2.23

```scheme
(define (for-each f items)
  (define (execute-and-iterate f items)
    (f (car items))
    (for-each f (cdr items)))

  (if (not (null? items))
    (execute-and-iterate f items)))

(for-each
  (lambda (x) (newline) (display x))
  (list 57 321 88))
; 57
; 321
; 88
; returns unspecified value
```

### Exercise 2.24

```text
1 ]=> (list 1 (list 2 (list 3 4)))
;Value: (1 (2 (3 4)))
```

This looks like an interesting list. Let us graph it, then.

![Image of the graph in cons-cell diagram form](/img/2-24.png)

Notice, that this graph represents three lists, each of length 2. This is different from `(list 1 2 3 4)`, which would return a single list of length 4.

### Exercise 2.25

```scheme
(car (cdr (car (cdr (cdr (list 1 3 (list 5 7) 9)))))) ; 7
(car (car (list (list 7)))) ; 7
(cdr (car (cdr (car (cdr (car (cdr (car (cdr (car (cdr (list 1 (list 2 (list 3 (list 4 (list 5 (list 6 7))))))))))))))))) ; 7
```

### Exercise 2.26

```scheme
(define x (list 1 2 3))
(define y (list 4 5 6))

; append appends two lists and combines their items
(append x y) ; (1 2 3 4 5 6)

; cons creates a cons pair of two items. Note that y is "linked" to the result
(cons x y) ; ((1 2 3) 4 5 6)

; list creates a list of the items it is provided with
(list x y) ; ((1 2 3) (4 5 6))
```

### Exercise 2.27

This is quite an interesting one. A reversal must also be done not only to the list in question, but to the items of the items if they do exist.

```scheme
(define (all-but-last items)
  (if (null? (cdr items))
    ()
    (cons (car items) (all-but-last (cdr items)))))
(all-but-last (list 23 72 149 34)) ; (23 72 149)

; deep-reverse reverses items and its subitems
(define (deep-reverse items)
  (cond
    ((null? items) items)
    ((not (list? items)) items)
    (else (cons (deep-reverse (car (last-pair items))) (deep-reverse (all-but-last items))))))

(define x (list (list 1 2) (list 3 4)))
(reverse x) ; ((3 4) (1 2))
(deep-reverse x) ; ((4 3) (2 1))
```

### Exercise 2.28

```scheme
; fringe takes in items and returns a single flattened list
(define (fringe items)
  (cond
    ((null? items) items)
    ((not (list? items)) (list items))
    (else (append (fringe (car items)) (fringe (cdr items))))))
(define x (list (list 1 2) (list 3 4)))
(fringe x) ; (1 2 3 4)
(fringe (list x x)) ; (1 2 3 4 1 2 3 4)
```

### Exercise 2.29

The following are the selectors for the `mobile` and `branch` structures defined by `make-mobile` and `make-branch`:

```scheme
; left-branch returns the left branch of a mobile
(define (left-branch mobile) (car mobile))

; right-branch returns the right branch of a mobile
(define (right-branch mobile) (car (cdr mobile)))

; branch-length returns the length of a branch
(define (branch-length branch) (car branch))

; branch-structure returns the structure attached to the branch
(define (branch-structure branch) (car (cdr branch)))
```

The following is an implementation for `total-weight`:

```scheme
; total-weight returns the total weight of a mobile. Returns itself if mobile is a number.
(define (total-weight mobile)
  (if (pair? mobile) ; i.e., mobile is represented by a pair i.e., it *is* a mobile
    (+ (total-weight (branch-structure (left-branch mobile)))
      (total-weight (branch-structure (right-branch mobile))))
    mobile))
```

Why I used `pair?` instead of `list?` is such that, in a later problem, the mobile and branch structures will be represented by `cons` instead of `list`. All `cons` are `list`s but not the other way around!

The following is an implementation for `balanced?`:

```scheme
; torque returns the torque of a branch
(define (torque branch)
  (* (branch-length branch) (total-weight (branch-structure branch))))

; balanced? checks if a mobile is balanced. Returns true if mobile is a number
(define (balanced? mobile)
  (if (not (pair? mobile))
    #t
    (= (torque (left-branch mobile))
      (torque (right-branch mobile)))))
```

Going to the fourth problem, by doing this, we would only need to change `(car (cdr ...))` to `(cdr ...)`:

```scheme
; left-branch returns the left branch of a mobile
(define (left-branch mobile) (car mobile))

; right-branch returns the right branch of a mobile
(define (right-branch mobile) (cdr mobile))

; branch-length returns the length of a branch
(define (branch-length branch) (car branch))

; branch-structure returns the structure attached to the branch
(define (branch-structure branch) (cdr branch))
```

### Exercise 2.30

```scheme
; square-tree squares a tree
(define (square-tree tree)
  (map (lambda (sub-tree)
      (if (pair? sub-tree)
        (square-tree sub-tree)
        (square sub-tree)))
    tree))
(square-tree
 (list 1
       (list 2 (list 3 4) 5)
       (list 6 7))) ; ==> (1 (4 (9 16) 25) (36 49))
```

### Exercise 2.31

```scheme
; tree-map maps f to tree such that element -> (f element)
(define (tree-map f tree)
  (map (lambda (sub-tree)
      (if (pair? sub-tree)
        (tree-map f sub-tree)
        (f sub-tree)))
    tree))
```

### Exercise 2.32

For each element `e` which is an element of `S`, all subsets of `S` will either have `e`, or not.

```scheme
(define (subsets s)
  (if (null? s)
    (list ())
    (let ((rest (subsets (cdr s))))
      (append
        rest
        (map (lambda (subset) (cons (car s) subset)) rest)))))
(subsets (list 1 2 3)) ; ==> (() (3) (2) (2 3) (1) (1 3) (1 2) (1 2 3))
```

The return value is the combination of `rest`, which are the subsets of `cdr s`, and `(map (lambda (subset) (cons (car s) subset)) rest)`, which is `car s` appended to each value of `rest`. Every element in the return value will either have `car s` or not.

### Exercise 2.33

`map` is defined as accumulating a list using `sequence` by repeatedly applying `(p elem)` to every `elem`:

```scheme
(define (map p sequence)
  (accumulate
    (lambda (x y) (cons (p x) y))
    ()
    sequence))
```

`append` performs a `cons` for every `elem` of `seq1` into `seq2`:

```scheme
(define (append seq1 seq2)
  (accumulate cons seq2 seq1))
```

`length` iterates the value by 1 every time an element is encountered:

```scheme
(define (length sequence)
  (accumulate
    (lambda (_ y) (+ y 1))
    0
    sequence))
```

### Exercise 2.34

In the problem statement, the keyword `higher-terms` was used, which was a bit of a misnomer and threw me off for a while.

```scheme
; horner-eval performs a Horner evaluation on coefficient-sequence with a particular x.
(define (horner-eval x coefficient-sequence)
  (accumulate
    (lambda (this-coeff higher-terms)
      (+ this-coeff (* higher-terms x)))
    0
    coefficient-sequence))
(horner-eval 2 (list 1 3 0 5 0 1)) ; ==> 79
```

### Exercise 2.35

```scheme
; count-leaves counts the number of leaves in t
(define (count-leaves t)
  (accumulate
    (lambda (current-value total)
      (+ total (length current-value)))
    0
    (map enumerate-tree t)))
```

### Exercise 2.36

```scheme
; accumulate-n takes in a sequence of sequences and accumulates using op and init.
(define (accumulate-n op init seqs)
  (if (null? (car seqs))
    ()
    (cons (accumulate op init (map car seqs))
      (accumulate-n op init (map cdr seqs)))))
(define s (list (list 1 2 3) (list 4 5 6) (list 7 8 9) (list 10 11 12)))
(accumulate-n + 0 s) ; ==> (22 26 30)
```

Inside the `cons` statement, we combine two values: the accumulated result of the first items of `seqs`, and the results of the remaining items of `seqs`. To get the first items of `seqs`, `(map car seqs)` is used, where every sequence is mapped to `car` thus returning the first item. Similarly, to get the remaining items of `seqs`, `(map cdr seqs)` is used.

### Exercise 2.37

```scheme
; matrix-*-vector performs a multiplication between a matrix and a vector
; and returns a vector
(define (matrix-*-vector m v)
  (map
    (lambda (row) (dot-product row v))
    m))

; Example from https://mathinsight.org/matrix_vector_multiplication
(matrix-*-vector
  (list
    (list 1 -1 2)
    (list 0 -3 1))
  (list 2 1 0)) ; (1 -3)

; transpose transposes a matrix
(define (transpose mat)
  (accumulate-n
    cons ; used to append each element for every column in the matrix
    ()
    mat))

; Example from https://en.wikipedia.org/wiki/Transpose
(transpose
  (list
    (list 1 2)
    (list 3 4)
    (list 5 6))) ; ((1 3 5) (2 4 6))

; matrix-*-matrix performs a multiplication between two matrices
(define (matrix-*-matrix m n)
  (let ((cols (transpose n)))
    (map
      (lambda (row)
        (matrix-*-vector cols row))
      m)))

; Example from https://mathinsight.org/matrix_vector_multiplication
(matrix-*-matrix
  (list
    (list 0 4 -2)
    (list -4 -3 0))
  (list
    (list 0 1)
    (list 1 -1)
    (list 2 3))) ; ((0 -10) (-3 -1))
```

### Exercise 2.38

For the first pair of statements:

```scheme
(fold-right / 1 (list 1 2 3))
; (/ 1 (fold-right / 1 (list 2 3)))
; (/ 1 (/ 2 (fold-right / 1 (list 3))))
; (/ 1 (/ 2 (/ 3 (fold-right / 1 ()))))
; (/ 1 (/ 2 (/ 3 1)))
; (/ 1 (/ 2 3))
; (/ 1 (0.667)) ; using floating-points instead of rationals for this showcasing
; ==> 1.5

(fold-left  / 1 (list 1 2 3))
; (iter 1 (list 1 2 3))
; (iter (/ 1 1) (list 2 3))
; (iter 1 (list 2 3))
; (iter (/ 1 2) (list 3))
; (iter 0.5 (list 3))
; (iter (/ 0.5 3) ())
; (iter 0.167 ())
; ==> 0.167
```

The first statement was $1 \div \left(2 \div 3\right)$, while the second one was $\left(1 \div 2\right) \div 3$

For the second pair of statements:

```scheme
(fold-right list () (list 1 2 3))
; (list 1 (fold-right list () (list 2 3)))
; (list 1 (list 2 (fold-right list () (list 3))))
; (list 1 (list 2 (list 3 (fold-right list () ()))))
; (list 1 (list 2 (list 3 ())))
; ==> (1 (2 (3 ())))

(fold-left  list () (list 1 2 3))
; (iter () (list 1 2 3))
; (iter (list () 1) (list 2 3))
; (iter (list (list () 1) 2) (list 3))
; (iter (list (list (list () 1) 2) 3) ())
; ==> (((() 1) 2) 3)
```

For `fold-left` and `fold-right` to have the same result, `(op a b)` must equal `(op b a)`, that is, the order of operations ought not matter.

### Exercise 2.39

```scheme
(define (reverse sequence)
  (fold-right
    (lambda (x y)
      (append y (list x)))
    ()
    sequence))
(reverse (list 1 2 3 4)) ; (4 3 2 1)

(define (reverse sequence)
  (fold-left
    (lambda (x y)
      (cons y x))
    ()
    sequence))
(reverse (list 1 2 3 4)) ; (4 3 2 1)
```

### Exercise 2.40

```scheme
; unique-pairs generates a sequence of (i,j) with 1<=j<i<=n.
(define (unique-pairs n)
  (flatmap
    (lambda (i)
      (map
        (lambda (j) (list i j))
        (enumerate-interval 1 (- i 1))))
    (enumerate-interval 1 n)))
(unique-pairs 6)

; prime-sum-pairs generates a sequence of (i,j) from unique-pairs
; such that i+j is prime
(define (prime-sum-pairs n)
  ; sum gets the sum of the values of a pair
  (define (sum p) (+ (car p) (cadr p)))
  (map
    (lambda (p) (append p (list (sum p))))
    (filter
      (lambda (p) (prime? (sum p)))
      (unique-pairs n))))
(prime-sum-pairs 6)
```

### Exercise 2.41

```scheme
; triples-with-sum returns a sequence of ordered pairs (i,j,k)
; such that i+j+k=s
(define (triples-with-sum s)
  (flatmap
    (lambda (i)
      (map
        (lambda (j)
          (list i j (- s i j)))
        (enumerate-interval 1 (- s i 1))))
    (enumerate-interval 1 s)))
(triples-with-sum 6) ; ((1 1 4) (1 2 3) (1 3 2) (1 4 1) (2 1 3) (2 2 2) (2 3 1) (3 1 2) (3 2 1) (4 1 1))
```

### Exercise 2.42

The convention I used for a position in the board would be a pair made using `cons`.

```scheme
; a position is represented using a cons where col, row are from 1 to n
; where the queens are arranged in an nxn grid
(define (position col row) (cons col row))

; col and row get the col and row of a position
(define (col position) (car position))
(define (row position) (cdr position))

; adjoin-position adjoins a new row-column position to a set of positions
(define (adjoin-position new-row k rest-of-queens)
  (append rest-of-queens (list (position k new-row))))
```

With regards to checking safety, `same-row?`, `same-col?` and `same-diag?` are written to check if two positions fall in the same row, column, or diagonal. I had to check for every pair of positions `(pos, key)` where `pos` is `positions` except `key`, and `key` is the only position which has a column `k`.

```scheme
; empty-board represents an empty set of positions
(define empty-board ())

; safe? determines whether the queen in the k'th column is safe w/ respect to others
(define (safe? k positions)
  ; suppose there are two positions a and b.
  ; let's do some checks...
  
  ; same-row? returns true if a, b have the same row
  (define (same-row? a b) (= (row a) (row b)))
  ; same-col? returns true if a, b have the same column
  (define (same-col? a b) (= (col a) (col b)))
  ; same-diag? returns true if a, b can be found diagonally
  (define (same-diag? a b)
    (= (abs (- (row a) (row b)))
       (abs (- (col a) (col b)))))

  ; relatively-safe? returns #t if a, b share neither row nor col nor diag
  (define (relatively-safe? a b)
    (and (not (same-row? a b))
         (not (same-col? a b))
         (not (same-diag? a b))))
  
  ; positions-but returns positions but itself
  (define (positions-but itself)
    (filter
      (lambda (pos)
        (not (and (= (row pos) (row itself))
                  (= (col pos) (col itself)))))
      positions))

  ; key-position returns the position whose column is k *and return the first value*
  (define (key-position k)
    (car
      (filter
        (lambda (pos) (= (col pos) k))
        positions)))

  ; all-true makes sure all of elems are equal to true
  (define (all-true elems)
    (accumulate
      (lambda (acc cnt)
        (if (not cnt) ; cnt == #f
            #f
            acc)) ; if acc were #f then cnt becomes #f and it stays #f
      #t
      elems))

  (let ((key (key-position k)))
    (all-true
      (map
        (lambda (pos) (relatively-safe? key pos))
        (positions-but key)))))
```

Running `(queens 8)` yields all 92 potential solutions to the Eight Queens puzzle.

```scheme
; queens returns all possible solutions to the eight-queens puzzle
(define (queens board-size)

  ; queen-cols list the possible solutions to eight-queens on a kxk grid
  (define (queen-cols k)
    (if (= k 0)
      (list empty-board)
      (filter
        (lambda (positions) (safe? k positions))
        (flatmap
          (lambda (rest-of-queens)
            (map (lambda (new-row) (adjoin-position new-row k rest-of-queens))
                 (enumerate-interval 1 board-size)))
          (queen-cols (- k 1))))))

  (queen-cols board-size))

(queens 8)
; ((1 . 1) (2 . 5) (3 . 8) (4 . 6) (5 . 3) (6 . 7) (7 . 2) (8 . 4))
; ((1 . 1) (2 . 6) (3 . 8) (4 . 3) (5 . 7) (6 . 4) (7 . 2) (8 . 5))
; ((1 . 1) (2 . 7) (3 . 4) (4 . 6) (5 . 8) (6 . 2) (7 . 5) (8 . 3))
; ((1 . 1) (2 . 7) (3 . 5) (4 . 8) (5 . 2) (6 . 4) (7 . 6) (8 . 3))
; ((1 . 2) (2 . 4) (3 . 6) (4 . 8) (5 . 3) (6 . 1) (7 . 7) (8 . 5))
; ((1 . 2) (2 . 5) (3 . 7) (4 . 1) (5 . 3) (6 . 8) (7 . 6) (8 . 4))
; ((1 . 2) (2 . 5) (3 . 7) (4 . 4) (5 . 1) (6 . 8) (7 . 6) (8 . 3))
; ((1 . 2) (2 . 6) (3 . 1) (4 . 7) (5 . 4) (6 . 8) (7 . 3) (8 . 5))
; ((1 . 2) (2 . 6) (3 . 8) (4 . 3) (5 . 1) (6 . 4) (7 . 7) (8 . 5))
; ((1 . 2) (2 . 7) (3 . 3) (4 . 6) (5 . 8) (6 . 5) (7 . 1) (8 . 4))
; ((1 . 2) (2 . 7) (3 . 5) (4 . 8) (5 . 1) (6 . 4) (7 . 6) (8 . 3))
; ((1 . 2) (2 . 8) (3 . 6) (4 . 1) (5 . 3) (6 . 5) (7 . 7) (8 . 4))
; ((1 . 3) (2 . 1) (3 . 7) (4 . 5) (5 . 8) (6 . 2) (7 . 4) (8 . 6))
; ((1 . 3) (2 . 5) (3 . 2) (4 . 8) (5 . 1) (6 . 7) (7 . 4) (8 . 6))
; ((1 . 3) (2 . 5) (3 . 2) (4 . 8) (5 . 6) (6 . 4) (7 . 7) (8 . 1))
; ((1 . 3) (2 . 5) (3 . 7) (4 . 1) (5 . 4) (6 . 2) (7 . 8) (8 . 6))
; ((1 . 3) (2 . 5) (3 . 8) (4 . 4) (5 . 1) (6 . 7) (7 . 2) (8 . 6))
; ((1 . 3) (2 . 6) (3 . 2) (4 . 5) (5 . 8) (6 . 1) (7 . 7) (8 . 4))
; ((1 . 3) (2 . 6) (3 . 2) (4 . 7) (5 . 1) (6 . 4) (7 . 8) (8 . 5))
; ((1 . 3) (2 . 6) (3 . 2) (4 . 7) (5 . 5) (6 . 1) (7 . 8) (8 . 4))
; ((1 . 3) (2 . 6) (3 . 4) (4 . 1) (5 . 8) (6 . 5) (7 . 7) (8 . 2))
; ((1 . 3) (2 . 6) (3 . 4) (4 . 2) (5 . 8) (6 . 5) (7 . 7) (8 . 1))
; ((1 . 3) (2 . 6) (3 . 8) (4 . 1) (5 . 4) (6 . 7) (7 . 5) (8 . 2))
; ((1 . 3) (2 . 6) (3 . 8) (4 . 1) (5 . 5) (6 . 7) (7 . 2) (8 . 4))
; ((1 . 3) (2 . 6) (3 . 8) (4 . 2) (5 . 4) (6 . 1) (7 . 7) (8 . 5))
; ((1 . 3) (2 . 7) (3 . 2) (4 . 8) (5 . 5) (6 . 1) (7 . 4) (8 . 6))
; ((1 . 3) (2 . 7) (3 . 2) (4 . 8) (5 . 6) (6 . 4) (7 . 1) (8 . 5))
; ((1 . 3) (2 . 8) (3 . 4) (4 . 7) (5 . 1) (6 . 6) (7 . 2) (8 . 5))
; ((1 . 4) (2 . 1) (3 . 5) (4 . 8) (5 . 2) (6 . 7) (7 . 3) (8 . 6))
; ((1 . 4) (2 . 1) (3 . 5) (4 . 8) (5 . 6) (6 . 3) (7 . 7) (8 . 2))
; ((1 . 4) (2 . 2) (3 . 5) (4 . 8) (5 . 6) (6 . 1) (7 . 3) (8 . 7))
; ((1 . 4) (2 . 2) (3 . 7) (4 . 3) (5 . 6) (6 . 8) (7 . 1) (8 . 5))
; ((1 . 4) (2 . 2) (3 . 7) (4 . 3) (5 . 6) (6 . 8) (7 . 5) (8 . 1))
; ((1 . 4) (2 . 2) (3 . 7) (4 . 5) (5 . 1) (6 . 8) (7 . 6) (8 . 3))
; ((1 . 4) (2 . 2) (3 . 8) (4 . 5) (5 . 7) (6 . 1) (7 . 3) (8 . 6))
; ((1 . 4) (2 . 2) (3 . 8) (4 . 6) (5 . 1) (6 . 3) (7 . 5) (8 . 7))
; ((1 . 4) (2 . 6) (3 . 1) (4 . 5) (5 . 2) (6 . 8) (7 . 3) (8 . 7))
; ((1 . 4) (2 . 6) (3 . 8) (4 . 2) (5 . 7) (6 . 1) (7 . 3) (8 . 5))
; ((1 . 4) (2 . 6) (3 . 8) (4 . 3) (5 . 1) (6 . 7) (7 . 5) (8 . 2))
; ((1 . 4) (2 . 7) (3 . 1) (4 . 8) (5 . 5) (6 . 2) (7 . 6) (8 . 3))
; ((1 . 4) (2 . 7) (3 . 3) (4 . 8) (5 . 2) (6 . 5) (7 . 1) (8 . 6))
; ((1 . 4) (2 . 7) (3 . 5) (4 . 2) (5 . 6) (6 . 1) (7 . 3) (8 . 8))
; ((1 . 4) (2 . 7) (3 . 5) (4 . 3) (5 . 1) (6 . 6) (7 . 8) (8 . 2))
; ((1 . 4) (2 . 8) (3 . 1) (4 . 3) (5 . 6) (6 . 2) (7 . 7) (8 . 5))
; ((1 . 4) (2 . 8) (3 . 1) (4 . 5) (5 . 7) (6 . 2) (7 . 6) (8 . 3))
; ((1 . 4) (2 . 8) (3 . 5) (4 . 3) (5 . 1) (6 . 7) (7 . 2) (8 . 6))
; ((1 . 5) (2 . 1) (3 . 4) (4 . 6) (5 . 8) (6 . 2) (7 . 7) (8 . 3))
; ((1 . 5) (2 . 1) (3 . 8) (4 . 4) (5 . 2) (6 . 7) (7 . 3) (8 . 6))
; ((1 . 5) (2 . 1) (3 . 8) (4 . 6) (5 . 3) (6 . 7) (7 . 2) (8 . 4))
; ((1 . 5) (2 . 2) (3 . 4) (4 . 6) (5 . 8) (6 . 3) (7 . 1) (8 . 7))
; ((1 . 5) (2 . 2) (3 . 4) (4 . 7) (5 . 3) (6 . 8) (7 . 6) (8 . 1))
; ((1 . 5) (2 . 2) (3 . 6) (4 . 1) (5 . 7) (6 . 4) (7 . 8) (8 . 3))
; ((1 . 5) (2 . 2) (3 . 8) (4 . 1) (5 . 4) (6 . 7) (7 . 3) (8 . 6))
; ((1 . 5) (2 . 3) (3 . 1) (4 . 6) (5 . 8) (6 . 2) (7 . 4) (8 . 7))
; ((1 . 5) (2 . 3) (3 . 1) (4 . 7) (5 . 2) (6 . 8) (7 . 6) (8 . 4))
; ((1 . 5) (2 . 3) (3 . 8) (4 . 4) (5 . 7) (6 . 1) (7 . 6) (8 . 2))
; ((1 . 5) (2 . 7) (3 . 1) (4 . 3) (5 . 8) (6 . 6) (7 . 4) (8 . 2))
; ((1 . 5) (2 . 7) (3 . 1) (4 . 4) (5 . 2) (6 . 8) (7 . 6) (8 . 3))
; ((1 . 5) (2 . 7) (3 . 2) (4 . 4) (5 . 8) (6 . 1) (7 . 3) (8 . 6))
; ((1 . 5) (2 . 7) (3 . 2) (4 . 6) (5 . 3) (6 . 1) (7 . 4) (8 . 8))
; ((1 . 5) (2 . 7) (3 . 2) (4 . 6) (5 . 3) (6 . 1) (7 . 8) (8 . 4))
; ((1 . 5) (2 . 7) (3 . 4) (4 . 1) (5 . 3) (6 . 8) (7 . 6) (8 . 2))
; ((1 . 5) (2 . 8) (3 . 4) (4 . 1) (5 . 3) (6 . 6) (7 . 2) (8 . 7))
; ((1 . 5) (2 . 8) (3 . 4) (4 . 1) (5 . 7) (6 . 2) (7 . 6) (8 . 3))
; ((1 . 6) (2 . 1) (3 . 5) (4 . 2) (5 . 8) (6 . 3) (7 . 7) (8 . 4))
; ((1 . 6) (2 . 2) (3 . 7) (4 . 1) (5 . 3) (6 . 5) (7 . 8) (8 . 4))
; ((1 . 6) (2 . 2) (3 . 7) (4 . 1) (5 . 4) (6 . 8) (7 . 5) (8 . 3))
; ((1 . 6) (2 . 3) (3 . 1) (4 . 7) (5 . 5) (6 . 8) (7 . 2) (8 . 4))
; ((1 . 6) (2 . 3) (3 . 1) (4 . 8) (5 . 4) (6 . 2) (7 . 7) (8 . 5))
; ((1 . 6) (2 . 3) (3 . 1) (4 . 8) (5 . 5) (6 . 2) (7 . 4) (8 . 7))
; ((1 . 6) (2 . 3) (3 . 5) (4 . 7) (5 . 1) (6 . 4) (7 . 2) (8 . 8))
; ((1 . 6) (2 . 3) (3 . 5) (4 . 8) (5 . 1) (6 . 4) (7 . 2) (8 . 7))
; ((1 . 6) (2 . 3) (3 . 7) (4 . 2) (5 . 4) (6 . 8) (7 . 1) (8 . 5))
; ((1 . 6) (2 . 3) (3 . 7) (4 . 2) (5 . 8) (6 . 5) (7 . 1) (8 . 4))
; ((1 . 6) (2 . 3) (3 . 7) (4 . 4) (5 . 1) (6 . 8) (7 . 2) (8 . 5))
; ((1 . 6) (2 . 4) (3 . 1) (4 . 5) (5 . 8) (6 . 2) (7 . 7) (8 . 3))
; ((1 . 6) (2 . 4) (3 . 2) (4 . 8) (5 . 5) (6 . 7) (7 . 1) (8 . 3))
; ((1 . 6) (2 . 4) (3 . 7) (4 . 1) (5 . 3) (6 . 5) (7 . 2) (8 . 8))
; ((1 . 6) (2 . 4) (3 . 7) (4 . 1) (5 . 8) (6 . 2) (7 . 5) (8 . 3))
; ((1 . 6) (2 . 8) (3 . 2) (4 . 4) (5 . 1) (6 . 7) (7 . 5) (8 . 3))
; ((1 . 7) (2 . 1) (3 . 3) (4 . 8) (5 . 6) (6 . 4) (7 . 2) (8 . 5))
; ((1 . 7) (2 . 2) (3 . 4) (4 . 1) (5 . 8) (6 . 5) (7 . 3) (8 . 6))
; ((1 . 7) (2 . 2) (3 . 6) (4 . 3) (5 . 1) (6 . 4) (7 . 8) (8 . 5))
; ((1 . 7) (2 . 3) (3 . 1) (4 . 6) (5 . 8) (6 . 5) (7 . 2) (8 . 4))
; ((1 . 7) (2 . 3) (3 . 8) (4 . 2) (5 . 5) (6 . 1) (7 . 6) (8 . 4))
; ((1 . 7) (2 . 4) (3 . 2) (4 . 5) (5 . 8) (6 . 1) (7 . 3) (8 . 6))
; ((1 . 7) (2 . 4) (3 . 2) (4 . 8) (5 . 6) (6 . 1) (7 . 3) (8 . 5))
; ((1 . 7) (2 . 5) (3 . 3) (4 . 1) (5 . 6) (6 . 8) (7 . 2) (8 . 4))
; ((1 . 8) (2 . 2) (3 . 4) (4 . 1) (5 . 7) (6 . 5) (7 . 3) (8 . 6))
; ((1 . 8) (2 . 2) (3 . 5) (4 . 3) (5 . 1) (6 . 7) (7 . 4) (8 . 6))
; ((1 . 8) (2 . 3) (3 . 1) (4 . 6) (5 . 2) (6 . 5) (7 . 7) (8 . 4))
; ((1 . 8) (2 . 4) (3 . 1) (4 . 3) (5 . 6) (6 . 2) (7 . 7) (8 . 5))
```

### Exercise 2.43

Let us first consider our original program:

```scheme
(flatmap
  (lambda (rest-of-queens)
    (map (lambda (new-row) (adjoin-position new-row k rest-of-queens))
         (enumerate-interval 1 board-size)))
  (queen-cols (- k 1))))
```

and let us look at Louis Reasoner's code:

```scheme
(flatmap
  (lambda (new-row)
    (map (lambda (rest-of-queens) (adjoin-position new-row k rest-of-queens))
         (queen-cols (- k 1))))
  (enumerate-interval 1 board-size))
```

We know that the order of operations have been swapped, but why does the second block of code run much, much slower than the first one? It took almost instantly to run `(queens 6)` originally, whereas it took around 4 seconds with the mistake.

Consider that, at the first block of code, that `queen-cols` should only be called once, as a parameter of `flatmap`. However, at the second block of code, `queen-cols` is called `board-size` number of times since, for every value of `(enumerate-interval 1 board-size)`, the value is passed onto the `lambda` which calls `queen-cols` every time that happpens.

It took around 91 milliseconds to run the Eight Queens problem but it took 70434 milliseconds to run Louis's version. I can't explain the discrepancy well but [this blogpost by Werner de Groot](https://wernerdegroot.wordpress.com/2015/08/01/sicp-exercise-2-43/) can.

### Exercise 2.44

```scheme
(define (up-split painter n)
  (if (= n 0)
      painter
      (let ((smaller (up-split painter (- n 1))))
        (below painter (beside smaller smaller)))))
```

### Exercise 2.45

```scheme
; split returns a "splitter" like right-split and up-split
; with a primary direction d1 and secondary direction d2
(define (split d1 d2)
  (define (splitter painter n)
      (if (= n 0)
          painter
          (let ((smaller (splitter painter (- n 1))))
            (d1 painter (d2 smaller smaller)))))
  splitter)
(define right-split (split beside below))
(define up-split (split below beside))
```

### Exercise 2.46

```scheme
; make-vect, xcor-vect, and ycor-vect implement a vector object.
(define (make-vect x y) (cons x y))
(define (xcor-vect v) (car v))
(define (ycor-vect v) (cdr v))

; add-vect, sub-vect, and scale-vect implement vector addition and scaling
(define (add-vect v1 v2)
  (make-vect (+ (xcor-vect v1) (xcor-vect v2))
             (+ (ycor-vect v1) (ycor-vect v2))))
(define (sub-vect v1 v2)
  (make-vect (- (xcor-vect v1) (xcor-vect v2))
             (- (ycor-vect v1) (ycor-vect v2))))
(define (scale-vect s v)
  (make-vect (* s (xcor-vect v))
             (* s (ycor-vect v))))
```

### Exercise 2.47

```scheme
(define (make-frame origin edge1 edge2)
  (list origin edge1 edge2))
(define (origin-frame f) (car f))
(define (edge1-frame f) (cadr f))
(define (edge2-frame f) (caddr f))
```

```scheme
(define (make-frame origin edge1 edge2)
  (cons origin (cons edge1 edge2)))
(define (origin-frame f) (car f))
(define (edge1-frame f) (cadr f))
(define (edge2-frame f) (cddr f))
```

### Exercise 2.48

```scheme
; make-segment, start-segment, and end-segment are getters and setters
; for segments represented by two vectors.
(define (make-segment v1 v2) (cons v1 v2))
(define (start-segment s) (car s))
(define (end-segment s) (cdr s))
```

### Exercise 2.49

```scheme
(define draw-outline
  (segments->painter
   (list
    (make-segment (make-vect 0.0 0.0) (make-vect 0.0 1.0))
    (make-segment (make-vect 0.0 1.0) (make-vect 1.0 1.0))
    (make-segment (make-vect 1.0 1.0) (make-vect 1.0 0.0))
    (make-segment (make-vect 1.0 0.0) (make-vect 0.0 0.0)))))

(define draw-diagonals
  (segments->painter
   (list
    (make-segment (make-vect 0.0 0.0) (make-vect 1.0 1.0))
    (make-segment (make-vect 0.0 1.0) (make-vect 1.0 0.0)))))

(define draw-varignon
  (segments->painter
   (list
    (make-segment (make-vect 0.5 0.0) (make-vect 1.0 0.5))
    (make-segment (make-vect 1.0 0.5) (make-vect 0.5 1.0))
    (make-segment (make-vect 0.5 1.0) (make-vect 0.0 0.5))
    (make-segment (make-vect 0.0 0.5) (make-vect 0.5 0.0)))))
```

The `wave` painter is too complex for me to represent here.

### Exercise 2.50

This requires a bit of spatial thinking to do. Just note that the base case has its origin at (0, 0), edge1's end at (1, 0), and edge2's end at (0, 1).

```scheme
(define (flip-horiz painter)
  (transform-painter painter
                     (make-vect 1.0 0.0)
                     (make-vect 0.0 0.0)
                     (make-vect 1.0 1.0)))

(define (rotate180 painter)
  (transform-painter painter
                     (make-vect 1.0 1.0)
                     (make-vect 0.0 1.0)
                     (make-vect 1.0 0.0)))

(define (rotate270 painter)
  (transform-painter painter
                     (make-vect 0.0 1.0)
                     (make-vect 0.0 0.0)
                     (make-vect 1.0 1.0)))
```

### Exercise 2.51

```scheme
(define (below painter1 painter2)
  (let ((split-point (make-vect 0.0 0.5)))
    (let ((paint-below (transform-painter
                        painter1
                        (make-vect 0.0 0.0)
                        (make-vect 1.0 0.0)
                        split-point))
          (paint-above (transform-painter
                        painter2
                        split-point
                        (make-vect 1.0 0.5)
                        (make-vect 0.0 1.0))))
      (lambda (frame)
        (paint-below frame)
        (paint-above frame)))))
```

Alternatively, we could define `below` using `beside` with some rotation. The following is a visualization:

![Representation on how to solve 2.51 using rotation and `beside`](/img/2-51.svg)

```scheme
(define (below painter1 painter2)
  (rotate90 (beside (rotate270 painter1)
                    (rotate270 painter2))))
```

### Exercise 2.52

As mentioned, `wave` is a bit too complex for me to represent here. The other problems can be solved though.

`corner-split` but using only one copy of `up-split` and `right-split` instead of two:

```scheme
(define (corner-split painter n)
  (if (= n 0)
      painter
      (beside (below painter (up-split painter (- n 1)))
              (below (right-split painter (- n 1)) (corner-split painter (- n 1))))))
```

`square-limit` that displays `rogers` outwards (the painter should be horizontally flipped):

```scheme
(define (square-limit painter n)
  (let ((quarter (corner-split (flip-horiz painter) n)))
    (let ((half (beside (flip-horiz quarter) quarter)))
      (below (flip-vert half) half))))
```

## 2.3 Symbolic Data

### Exercise 2.53

```scheme
(list 'a 'b 'c)
; ==> (a b c)
(list (list 'george))
; ==> ((george))
(cdr '((x1 x2) (y1 y2)))
; ==> ((y1 y2))
(cadr '((x1 x2) (y1 y2)))
; ==> (y1 y2)
(pair? (car '(a short list)))
; ==> #f
(memq 'red '((red shoes) (blue socks)))
; ==> #f
(memq 'red '(red shoes blue socks))
; ==> (red shoes blue socks)
```

### Exercise 2.54

```scheme
(define (equal? x y)
  (cond
    ((and (null? x) (null? y)) #t)
    ((or (null? x) (null? y)) #f)
    (else (and (eq? (car x) (car y))
               (equal? (cdr x) (cdr y))))))

(equal? (list 'a 'b 'c) (list 'a 'b 'c))    ; #t
(equal? (list 'a 'b 'c) (list 'a 'b 'c 'd)) ; #f
```

### Exercise 2.55

Consider that `'abracadabra` provides the symbol `abracadabra`. It is interesting to note what `''abracadabra` (representing the symbol *of* the symbol `abracadabra`) yields:

```scheme
'abracadabra
; ==> abracadabra
''abracadabra
; ==> (quote abracadabra)
```

Consider then that `'a` is actually a shorthand for `(quote a)`. Because of this, `''a` is simply `'(quote a)`, which would yield `(quote a)`.

```scheme
(car ''abracadabra)
; (car '(quote abracadabra))
; ==> quote
```

### Exercise 2.56

```scheme
(define (make-exponentiation b e)
  (cond ((=number? e 0) b)
        ((=number? b 1) 1)
        ((and (number? b) (number? e)) (expt b e))
        (else (list '** b e))))
(define (exponentiation? x) (and (pair? x) (eq? (car x) '**)))
(define (base e) (cadr e))
(define (exponent e) (caddr e))

(define (deriv exp var)
  (cond
    ; other conditions go here
    ((exponentiation? exp)
     (make-product
      (make-product
       (exponent exp)
       (make-exponentiation (base exp) (- (exponent exp) 1)))
      (deriv (base exp) var)))
    (else (error "unknown expression type: DERIV" exp))))
```

### Exercise 2.57

I had to weed out the constants from `addends` and separating their sum from the remaining elements. In addition, I had to change the definition of `augend` to allow for arbitrary-length expressions:

```scheme
; make-sum creates a sum from variadic parameter addends.
; Sums first the constants and then creates this recursive definition
; such that (a+b+c) == (a+(b+c)).
(define (make-sum . addends)
  ; sum-constantless sums addends recursively
  ; where addends has no constant.
  (define (sum-constantless addends)
    (if (= (length addends) 1)
        (car addends)
        (list '+ (car addends) (sum-constantless (cdr addends)))))

  (let ((constants-sum (accumulate + 0 (filter number? addends)))
        (remaining (filter (lambda (x) (not (number? x))) addends)))

    (cond ((null? remaining) constants-sum)
          ((= constants-sum 0) (sum-constantless remaining))
          (else (list '+ constants-sum (sum-constantless remaining))))))


(define (sum? x) (and (pair? x) (eq? (car x) '+)))
(define (addend s) (cadr s))
(define (augend s)
  (if (= (length (cddr s)) 1)
      (caddr s)
      (apply make-sum (cddr s))))
```

A similar process is going on with `make-product`

```scheme
; make-product returns a product from a set of factors
(define (make-product . factors)
  ; product-constantless multiplies recursively where factors has no constant
  (define (product-constantless factors)
    (if (= (length factors) 1)
        (car factors)
        (list '* (car factors) (product-constantless (cdr factors)))))

  (let ((constants-product (accumulate * 1 (filter number? factors)))
        (remaining (filter (lambda (x) (not (number? x))) factors)))

    (cond ((null? remaining) constants-product)
          ((= constants-product 0) 0)
          ((= constants-product 1) (product-constantless remaining))
          (else (list '* constants-product (product-constantless remaining))))))

(define (product? x) (and (pair? x) (eq? (car x) '*)))
(define (multiplier p) (cadr p))
(define (multiplicand p)
  (if (= (length (cddr p)) 1)
      (caddr p)
      (apply make-product (cddr p))))
```

### Exercise 2.58

The first part is a bit of an exercise.

```scheme
(define (make-sum a1 a2)
  (cond ((and (number? a1) (number? a2)) (+ a1 a2))
        ((=number? a1 0) a2)
        ((=number? a2 0) a1)
        (else (list a1 '+ a2))))
(define (sum? x) (and (pair? x) (eq? (cadr x) '+)))
(define (addend s) (car s))
(define (augend s) (caddr s))

(define (make-product m1 m2)
  (cond ((and (number? m1) (number? m2)) (* m1 m2))
        ((or (=number? m1 0) (=number? m2 0)) 0)
        ((=number? m1 1) m2)
        ((=number? m2 1) m1)
        (else (list m1 '* m2))))
(define (product? x) (and (pair? x) (eq? (cadr x) '*)))
(define (multiplicand p) (car p))
(define (multiplier p) (caddr p))

(deriv '(x + 3) 'x) ; ==> 1
(deriv '(x * y) 'x) ; ==> y
(deriv '((x * y) * (x + 3)) 'x) ; ==> (((x + 3) * y) + (x * y))
(deriv '(x + (3 * (x + (y + 2)))) 'x) ; ==> 4
```

The second part is a lot more difficult. Checks have to be made to ensure that the precedence of multiplication over addition is maintained. I have not done a solution for this.

### Exercise 2.59

```scheme
(define (union-set set1 set2)
  (cond ((null? set1) set2)
        ((null? set2) set1)
        ((element-of-set? (car set1) set2) (union-set (cdr set1) set2))
        (else (cons (car set1) (union-set (cdr set1) set2)))))

(intersection-set '(a b c d) '(c e f g)) ; ==> (c)
(union-set '(a b c d) '(c e f g)) ; ==> (a b d c e f g)
```

### Exercise 2.60

`element-of-set?` and `intersection-set` wouldn't change, although `adjoin-set` wouldn't need to check if an element is in the set, and `union-set` would just recursively add elements regardless whether or not they are already present:

```scheme
(define (element-of-set? x set)
  (cond ((null? set) #f)
        ((eq? x (car set)) #t)
        (else (element-of-set? x (cdr set)))))

(define (adjoin-set x set) (cons x set))

(define (intersection-set set1 set2)
  (cond ((or (null? set1) (null? set2)) '())
        ((element-of-set? (car set1) set2)
         (cons (car set1) (intersection-set (cdr set1) set2)))
        (else (intersection-set (cdr set1) set2))))

(define (union-set set1 set2)
  (cond ((null? set1) set2)
        ((null? set2) set1)
        (else (cons (car set1) (union-set (cdr set1) set2)))))

(intersection-set '(a b c d) '(c e f g)) ; ==> (c)
(union-set '(a b c d) '(c e f g)) ; ==> (a b c d c e f g)
```

While not checking for presence by `adjoin-set` can be seen as a benefit, and `union-set` will be $O\left(n\right)$ since it will just be recursively pushing elements, the sets would become substantially larger as more operations are placed on them, and this will be detrimental for operations which might have to check for `element-of-set?`. For instance, if there are some unique elements at the end of the list representation, and a lot of duplicates at the start, `element-of-set?` will take a much longer time to go through a set to find these unique elements.

### Exercise 2.61

```scheme
(define (adjoin-set x set)
  (cond ((null? set) (list x))
        ((< x (car set)) (cons x set))
        ((= x (car set)) set)
        (else (cons (car set) (adjoin-set x (cdr set))))))
(adjoin-set 3 '(1 2 4 5)) ; ==> (1 2 3 4 5)
(adjoin-set 1 '(2 3 4 5)) ; ==> (1 2 3 4 5)
(adjoin-set 2 '(1 2 4 5)) ; ==> (1 2 4 5)
(adjoin-set 5 '(1 2 3 4)) ; ==> (1 2 3 4 5)
```

### Exercise 2.62

```scheme
(define (union-set set1 set2)
  (cond ((null? set1) set2)
        ((null? set2) set1)
        (else
         (let ((x1 (car set1)) (x2 (car set2)))
           (cond ((= x1 x2)
                  (cons x1 (union-set (cdr set1) (cdr set2))))
                 ((< x1 x2)
                  (cons x1 (union-set (cdr set1) set2)))
                 ((> x1 x2)
                  (cons x2 (union-set set1 (cdr set2)))))))))

(union-set '(1 2 5) '(2 4 6)) ; ==> (1 2 4 5 6)
```

### Exercise 2.63

Each of the three trees in Figure 2.16 can be expressed as follows:

```scheme
(define t1
  '(7
    (3 (1 () ())
       (5 () ()))
    (9 ()
       (11 () ()))))
(define t2
  '(3
    (1 () ())
    (7 (5 () ())
       (9 ()
          (11 () ())))))
(define t3
  '(5
    (3 (1 () ())
       ())
    (9 (7 () ())
       (11 () ()))))
```

Both `tree->list-1` and `tree->list-2` produce the same results for each of the three trees:

```scheme
(tree->list-1 t1) ; ==> (1 3 5 7 9 11)
(tree->list-2 t1) ; ==> (1 3 5 7 9 11)
(tree->list-1 t2) ; ==> (1 3 5 7 9 11)
(tree->list-2 t2) ; ==> (1 3 5 7 9 11)
(tree->list-1 t3) ; ==> (1 3 5 7 9 11)
(tree->list-2 t3) ; ==> (1 3 5 7 9 11)
```

Let us investigate each of their behaviors:

```scheme
;  (tree->list-1 t1)
;  (append (tree->list-1 (left-branch t1))
;          (cons (entry t1) (tree->list-1 (right-branch t1))))
;  (append (tree->list-1 '(3 (1 () ()) (5 () ())))
;          (cons 7 (tree->list-1 '(9 () (11 () ())))))
;  (append
;   (append (tree->list-1 '(1 () ()))
;           (cons 3 (tree->list-1 '(5 () ()))))
;    (cons 7
;          (append (tree->list-1 '())
;                  (cons 9 (tree->list-1 '(11 () ()))))))
;  (append
;   (append (append (tree->list-1 '())
;                   (cons 1 (tree->list-1 '())))
;           (cons 3 (append (tree->list-1 '())
;                           (cons 5 (tree->list-1 '())))))
;   (cons 7
;         (append '()
;                 (cons 9 (append (tree->list-1 '())
;                                 (cons 11 (tree->list-1 '())))))))
;  (append
;   (append (append '()
;                   (cons 1 '()))
;           (cons 3 (append '()
;                           (cons 5 '()))))
;   (cons 7
;         (append '()
;                 (cons 9 (append '()
;                                 (cons 11 '()))))))
;  (append
;   (append '(1)
;           '(3 5))
;   (cons 7
;         (append '()
;                 '(9 11))))
;  ==> '(1 3 5 7 9 11)
```

`tree->list-1` is a tree-recursive function which does an `append` every time it is called with a non-empty argument. Note that `append` is a very costly function as it has to traverse to the end of the list every time it is called, and every succeeding call to `append` will have an argument longer than the previous one.

```scheme
(tree->list-2 t1)
; (copy-to-list t1 '())
; (copy-to-list
;  (left-branch t1)
;  (cons 7 (copy-to-list (right-branch t1)
;                        '())))
; (copy-to-list
;  '(3 (1 () ()) (5 () ()))
;  (cons 7 (copy-to-list
;           '(9 () (11 () ()))
;           '())))
; (copy-to-list
;  '(3 (1 () ()) (5 () ()))
;  (cons 7 (copy-to-list
;           '()
;           (cons 9 (copy-to-list
;                    '(11 () ())
;                    '())))))
; (copy-to-list
;  '(3 (1 () ()) (5 () ()))
;  (cons 7 (cons 9 (copy-to-list
;                   '()
;                   (cons 11 (copy-to-list '() '()))))))
; (copy-to-list
;  '(3 (1 () ()) (5 () ()))
;  (cons 7 (cons 9 (cons 11 '()))))
; (copy-to-list '(3 (1 () ()) (5 () ()))
;               '(7 9 11))
; (copy-to-list '(1 () ())
;               (cons 3 (copy-to-list '(5 () ()) '(7 9 11))))
; (copy-to-list '(1 () ())
;               (cons 3 (copy-to-list '()
;                                     (cons 5 (copy-to-list '() '(7 9 11))))))
; (copy-to-list '(1 () ())
;               (cons 3 (cons 5 '(7 9 11))))
; (copy-to-list '(1 () ()) '(3 5 7 9 11))
; (copy-to-list '()
;               (cons 1 (copy-to-list '() '(3 5 7 9 11))))
; (cons 1 '(3 5 7 9 11))
; ==> '(1 3 5 7 9 11)
```

`tree->list-2` uses a helper function `copy-to-list` which combines lists using `cons` after every call. `cons` is a constant time procedure compared to `append`.

The latter procedure will take a shorter time than the former. By how much is something which I cannot be certain of.
