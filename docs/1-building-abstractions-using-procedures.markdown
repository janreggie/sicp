# Building Abstractions Using Procedures

## 1.1 The Elements of Programming

### Exercise 1.1

```scheme
10
; 10
(+ 5 3 4)
; 12
(- 9 1)
; 8
(/ 6 2)
; 3
(+ (* 2 4) (- 4 6))
; 6
(define a 3)
; a = 3
(define b (+ a 1))
; b = 4
(+ a b (* a b))
; 19
(= a b)
; #f
(if (and (> b a) (< b (* a b)))
  b
  a)
; 4
(cond ((= a 4) 6)
  ((= b 4) (+ 6 7 a))
  (else 25))
; (+ 6 7 a) => 16
(+ 2 (if (> b a) b a))
; 6
(* (cond ((> a b) a)
    ((< a b) b)
    (else -1))
  (+ a 1))
; 16
```

### Exercise 1.2

```scheme
(/ (+ 5 4 (- 2 (- 3 (+ 6 (/ 4 5)))))
  (* 3 (- 6 2) (- 2 7)))
```

### Exercise 1.3

```scheme
; sum-of-squares takes in two numbers and returns the sum of their squares
(define (sum-of-squares a b) (+ (* a a) (* b b)))
; exercise-1-3 takes in three numbers
; and returns the sum of squares of the two larger numbers
(define (exercise-1-3 a b c) (
  cond ((and (< b a) (< b c)) (sum-of-squares a c))
    ((and (< a b) (< a c)) (sum-of-squares b c))
    (else (sum-of-squares a b))
) )
```

### Exercise 1.4

```scheme
(define (a-plus-abs-b a b)
  ((if (> b 0) + -) a b))
; the operator changes depending on the value of the if statement!!
; if b>0 return a+b otherwise return a-b (which turns b positive and adds it to a)
```

### Exercise 1.5

```scheme
(define (p) (p))  ; a recursive function (don't execute this!!)
(define (test x y) (if (= x 0) 0 y))

(test 0 (p))  ; don't run this on applicative-order systems
```

On normal-order evaluation, the expression `(test 0 (p))` first expands to `(if (= 0 0) 0 (p))`, which will be evaluated to `0`. On applicative-order evaluation, the expression `(test 0 (p))` will have `(p)` expanded to... `(p)`, and then expanded to `(p)` recursively, leading to no real work being done.

### Exercise 1.6

Substituting this `new-if` function in the procedure causes a `maximum recursion depth exceeded` error, even for an input of `1`. Why?

```scheme
(sqrt 1)
; ==> (sqrt-iter 1.0 1)
; ==> (new-if (good-enough? 1.0 1) 1.0 (sqrt-iter (improve guess x) x))
```

Here lies the kicker. Before `new-if` gets substituted, it first has to evaluate the arguments `(good-enough? 1.0 1)`, which easily evaluates to `#t`, and `(sqrt-iter (improve guess x) x)`, which does a recursive loop. The stack continues to grow until maximum recursion depth is reached.

### Exercise 1.7

```scheme
; eval-sqrt evaluates the sqrt function for a number
(define (eval-sqrt x) (- (square (sqrt x)) x))
(eval-sqrt 4.64e-35)      ; ==> .0009765625, or 9.765625e-4
(eval-sqrt 104828495672)  ; ==> -.0000152587890625
```

Notice two things here.
The first one is that the evaluation of the square root of the very small number has a ridiculously large error, where it is off by several orders of magnitude. (The real value of the square root is 6.8117e-18.) This is expected since `good-enough` checks if the difference between the values is less than some constant threshold: good for most cases, but bad for numbers that are smaller than said threshold.

The second one is that there is always some amount of error when dealing with floating point numbers, as shown in the second example. Some precision will always be lost when dealing with floats.

Redefining `good-enough` to check relative to `guess`:

```scheme
; good-enough checks if the difference between the current and next guess
; is less than 0.0001% of the current value of guess
(define (good-enough guess x)
  (< (abs (- guess (improve guess x))) (/ guess 100000)))
(eval-sqrt 4.64e-35)      ; ==> 2.800177998007718e-41
(eval-sqrt 104828495672)  ; ==> 991925.5386352539
```

While the value for error might seem much larger for large numbers, running `(sqrt 104828495672)` yields 323773.8216680568, not too far off from the real value of 323772.289846. In addition, running `(sqrt 4.64e-35)` yields 6.811756601771674e-18, really close to the actual value.

### Exercise 1.8

```scheme
; cbrt solves the cube root using Newton's method
(define (cbrt x)
  (define (cbrt-iter guess x)
    (if (cbrt-goodenough guess x) guess (cbrt-iter (cbrt-improve guess x) x)))
  (define (cbrt-improve guess x)
    (/ (+ (/ x (* guess guess)) (* 2 guess)) 3))
  (define (cbrt-goodenough guess x)
    (< (abs (- guess (cbrt-improve guess x)))
      (/ guess 100000)))
(cbrt-iter 1.0 x))
(cbrt 27)  ; ==> 3.0000005410641766
```

## 1.2 Procedures and the Processes they Generate

### Exercise 1.9

Supposing `inc` and `dec` are increment and decrement operators respectively, there is a difference how these two functions work:

```scheme
; First process
(define (+ a b)
  (if (= a 0) b (inc (+ (dec a) b))))
(+ 4 5)
; (inc (+ (dec 4) 5))
; (inc (+ 3 5))
; (inc (inc (+ (dec 3) 5)))
; (inc (inc (+ 2 5)))
; (inc (inc (inc (+ (dec 2) 5))))
; (inc (inc (inc (+ 1 5))))
; (inc (inc (inc (inc (+ (dec 1) 5)))))
; (inc (inc (inc (inc (+ 0 5)))))
; (inc (inc (inc (inc 5))))
; (inc (inc (inc 6)))
; (inc (inc 7))
; (inc 8)
; (9)
```

```scheme
; Second process
(define (+ a b)
  (if (= a 0) b (+ (dec a) (inc b))))
(+ 4 5)
; (+ (dec 4) (inc 5))
; (+ 3 6)
; (+ (dec 3) (inc 6))
; (+ 2 7)
; (+ (dec 2) (inc 7))
; (+ 1 8)
; (+ (dec 1) (inc 8))
; (+ 0 9)
; (9)
```

The first process can be characterized as recursive since a chain of operations can be seen growing after every call, while the second can be characterized as iterative as the chain of operations does not grow or shrink, and the state is maintained by the parameters it contains.

### Exercise 1.10

Consider Ackermann's function:

```scheme
(define (A x y)
  (cond ((= y 0) 0)
    ((= x 0) (* 2 y))
    ((= y 1) 2)
    (else (A (- x 1) (A x (- y 1))))))
```

From here, we see that `f` such that `(define (f n) (A 0 n))` would just be $f\left(n\right)=2n$.

```scheme
(A 1 10)
; (A (- 1 1) (A 1 (- 10 1)))
; (A 0 (A 1 9))
; (A 0 (A (- 1 1) (A 1 (- 9 1))))
; (A 0 (A 0 (A 1 8)))
; (A 0 (A 0 (A (- 1 1) (A 1 (- 8 1)))))
; (A 0 (A 0 (A 0 (A 1 7))))
; (A 0 (A 0 (A 0 (A (- 1 1) (A 1 (- 7 1))))))
; (A 0 (A 0 (A 0 (A 0 (A 1 6)))))
; (A 0 (A 0 (A 0 (A 0 (A (- 1 1) (A 1 (- 6 1)))))))
; (A 0 (A 0 (A 0 (A 0 (A 0 (A 1 5))))))
; (A 0 (A 0 (A 0 (A 0 (A 0 (A (- 1 1) (A 1 (- 5 1))))))))
; (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A 1 4)))))))
; (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A (- 1 1) (A 1 (- 4 1)))))))))
; (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A 1 3))))))))
; (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A (- 1 1) (A 1 (- 3 1))))))))))
; (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A 1 2)))))))))
; (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A (- 1 1) (A 1 (- 2 1)))))))))))
; (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A 1 1))))))))))
; (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 2)))))))))
; (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (* 2 2)))))))))
; (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 4))))))))
; (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (* 2 4))))))))
; (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 8)))))))
; (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 (* 2 8)))))))
; (A 0 (A 0 (A 0 (A 0 (A 0 (A 0 16))))))
; (A 0 (A 0 (A 0 (A 0 (A 0 (* 2 16))))))
; (A 0 (A 0 (A 0 (A 0 (A 0 32)))))
; (A 0 (A 0 (A 0 (A 0 (* 2 32)))))
; (A 0 (A 0 (A 0 (A 0 64))))
; (A 0 (A 0 (A 0 (* 2 64))))
; (A 0 (A 0 (A 0 128)))
; (A 0 (A 0 (* 2 128)))
; (A 0 (A 0 256))
; (A 0 (* 2 256))
; (A 0 512)
; (* 2 0 512)
; (1024)
```

Hypothesize that `g` such that `(define (g n) (A 1 n))` equals $g\left(n\right)=2^n$. This can be proved using induction: suppose $A\left(1,n\right)=2^n$, and prove that $A\left(1,n+1\right)=2^{n+1}$.

$$
\begin{aligned}
A\left(1,n+1\right) &= A\left(1-1, A\left(1, \left(n+1\right)-1\right)\right) \\
                    &= A\left(0, A\left(1, n\right)\right) \\
                    &= 2\cdot A\left(1,n\right) \\
                    &= 2\cdot2^n \\
                    &= 2^{n+1}
\end{aligned}
$$

```scheme
(A 2 4)
; (A (- 2 1) (A 2 (- 4 1)))
; (A 1 (A 2 3))
; (A 1 (A (- 2 1) (A 2 (- 3 1))))
; (A 1 (A 1 (A 2 2)))
; (A 1 (A 1 (A (- 2 1) (A 2 (- 2 1)))))
; (A 1 (A 1 (A 1 (A 2 1))))
; (A 1 (A 1 (A 1 2)))
```

From our previous definition of `g`, we can say that the expression `(A 1 (A 1 (A 1 2)))` solves to $2^{2^{2^2}}$, although writing down the steps to getting there will be ~~hell~~ an exercise left to the reader.

Hypothesize that `h` such that `(define (h n) (A 2 n))` equals $h\left(n\right)=2^{2^{\cdot^{\cdot^{\cdot^2}}}}$, such that the number of $2$ equals $n$. This also can be proved using induction: suppose $A\left(2,n\right)=2^{2^{\cdot^{\cdot^{\cdot^2}}}} \rbrace\text{n-many 2's}$, and prove that $A\left(2,n+1\right)$ results to $n+1$ twos:

$$
\begin{aligned}
A\left(2,n+1\right) &= A\left(2-1, A\left(2, \left(n+1\right)-1\right)\right) \\
                    &= A\left(1,A\left(2,n\right)\right) \\
                    % why do i even bother...
                    &= A\left(1, \left.2^{2^{\cdot^{\cdot^{\cdot^2}}}}\right\rbrace\text{$n$-many 2's}\right) \\
                    &= 2^{\left.2^{2^{\cdot^{\cdot^{\cdot^2}}}}\right\rbrace\text{$n$-many 2's}} \\
                    &= \left.2^{2^{\cdot^{\cdot^{\cdot^2}}}}\right\rbrace\text{$n+1$-many 2's}
\end{aligned}
$$
