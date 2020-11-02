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
