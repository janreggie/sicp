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

### Exercise 1.11

Writing the recursive implementation is trivial:

```scheme
(define (f n)
  (if (< n 3)
    n
    (+ (f (- n 1))
      (* 2 (f (- n 2)))
      (* 3 (f (- n 3))))))
(f 30)  ; ==> 61354575194 (will take a long time to compute)
```

Writing an iterative implementation is a bit more difficult.
Consider that, ultimately, `f` is evaluated as a sum of three numbers,
and these three numbers can be used as a state.

```scheme
(define (f n)
  ; iter is the iterative process wherein (a, b, c) <- (a+2b+3c, a, b).
  ; if count == 0, return a
  (define (iter a b c count)
    (if (= count 0)
      a
      (iter (+ a (* 2 b) (* 3 c)) a b (- count 1))))

  (if (< n 3)
    n
    (iter 2 1 0 (- n 2)))  ; 2 as an offset
)
(f 30)  ; ==> 61354575194 (didn't take that long at all!)
```

### Exercise 1.12

```scheme
; pascal returns the cnt'th number (start from zero)
; at the row'th row (0: 1, 1: 1,1, 2: 1,2,1).
(define (pascal row cnt)
  (cond ((or (< cnt 0) (> cnt row)) 0)
    ((or (= cnt 0) (= cnt row)) 1)
    (else (+
      (pascal (- row 1) (- cnt 1))
      (pascal (- row 1) cnt))
    )
  )
)
(pascal 4 2)
```

### Exercise 1.13

Initially, let us prove that $F\left(n\right) = \frac{\phi^n - \psi^n}{\sqrt{5}}$, where $F\left(n\right)$ is the $n$'th Fibonacci number and $\phi=\frac{1+\sqrt{5}}{2}, \psi=\frac{1-\sqrt{5}}{2}$, via induction.

The base cases for $F\left(0\right)$ and $F\left(1\right)$ is shown to be 0 and 1. A proof is left as an exercise to the reader.

Suppose that $F$ follows up to $n-1$. Let us then prove that $F\left(n\right)$ holds.

$$
\begin{aligned}
F\left(n\right) &= F\left(n-1\right) + F\left(n-2\right)  \\
                &= \frac{\phi^\left(n-1\right) - \psi^\left(n-1\right)}{\sqrt{5}}
                    + \frac{\phi^\left(n-2\right) - \psi^\left(n-2\right)}{\sqrt{5}} \\
                &= \frac{\left(\phi+1\right) \phi^\left(n-2\right) - \left(\psi+1\right) \psi^\left(n-2\right)}{\sqrt{5}} \\
                &= \frac{\frac{3+\sqrt{5}}{2} \phi^\left(n-2\right) - \frac{3-\sqrt{5}}{2} \psi^\left(n-2\right)}{\sqrt{5}}
                  && \text{Note that $\frac{3\pm\sqrt{5}}{2}=\left(\frac{1\pm\sqrt{5}}{2}\right)^2$} \\
                &= \frac{\phi^2 \phi^\left(n-2\right) - \psi^2 \psi^\left(n-2\right)}{\sqrt{5}} \\
                &= \frac{\phi^n - \psi^n}{\sqrt{5}}
\end{aligned}
$$

Note that $\psi\approx-0.618$ and $\psi^n$ approaches zero. Therefore, $\frac{\phi^n}{\sqrt{5}}$ is "close enough" to $\frac{\phi^n - \psi^n}{\sqrt{5}}$.

### Exercise 1.14

![Image of the tree](/img/1-14.svg)

Paths leading to a red node are unwanted, whereas paths leading to a green node are desired. Note that multiple sections of the tree repeat itself, which is why a node can have more than two paths coming towards it.

An increment to `amount` increases the number of operations exponentially, and increases the number of nodes to compute linearly.

### Exercise 1.15

```scheme
(define (cube x) (* x x x))
(define (p x) (- (* 3 x) (* 4 (cube x))))
(define (sine angle)
  (if (not (> (abs angle) 0.1))
    angle
    (p (sine (/ angle 3.0)))))
(sine 12.15)
; (/ angle 3.0) and (p x) operations have been substituted
; (p (sine 4.05))
; (p (p (sine 1.35)))
; (p (p (p (sine 0.45))))
; (p (p (p (p (sine 0.15)))))
; (p (p (p (p (p (sine 0.05))))))
; (p (p (p (p (p 0.05)))))
; (p (p (p (p 0.1495))))
; (p (p (p 0.4351)))
; (p (p 0.9758))
; (p -0.7892)
; -0.4044
```

The `p` procedure has been applied five times. Considering that `p` can be solved in constant time and occupies constant space, the order of growth in space and the number of steps for $p\left(a\right)$ is $\Theta\left(\lg n\right)$.

This can be shown by noticing that $p\left(3a\right)$ requires a constant number of operations more than $p\left(a\right)$, for instance, the amount of space and operations for `(sine 1.35)` versus that of `(sine 4.05)`.

### Exercise 1.16

```scheme
; expt is an exponential function that returns b raised to n.
; note that this shadows the built-in expt.
(define (expt b n)
  (define (even? n) (= (remainder n 2) 0))
  (define (halve n) (/ n 2))
  (define (square n) (* n n))
  ; exptiter iterates thru a, b, and n until b equals 1, and then the result is located in a.
  ; a must be initialized to 1.
  (define (exptiter a b n)
    (cond ((= n 0) a)
      ((even? n) (exptiter a (square b) (halve n)))
      (else (exptiter (* a b) b (- n 1)))))
  (exptiter 1 b n))
(expt 3 5) ; ==> 243
```

### Exercise 1.17

```scheme
(define (mul a b)
  (define (even? n) (= (remainder n 2) 0))
  (define (halve n) (/ n 2))
  (define (double n) (+ n n))
  (cond
    ((= b 0) 0)
    ((= b 1) a)
    ((even? b) (mul (double a) (halve b)))
    (else (+ a (mul a (- b 1))))))
(mul 9 6) ; ==> 54
```

### Exercise 1.18

```scheme
(define (mul a b)
  (define (even? n) (= (remainder n 2) 0))
  (define (halve n) (/ n 2))
  (define (double n) (+ n n))
  (define (multiter a b result)
    (cond ((= b 0) result)
      ((even? b) (multiter (double a) (halve b) result))
      (else (multiter a (- b 1) (+ result a)))))
  (multiter a b 0))
(mul 9 6) ; ==> 54
```

### Exercise 1.19

Note that $a, b \xleftarrow{T\left(p,q\right)} bq+aq+ap, bp+aq = a\left(p+q\right)+bq, aq+bp$. With some algebra,

$$
\begin{aligned}
a, b &\xleftarrow{T^2\left(p,q\right)} \left(ap^2+2apq+2bpq+2aq^2+bq^2\right), \left(bp^2+2apq+aq^2+bq^2\right) \\
     &\xleftarrow{T^2\left(p,q\right)} a\left(p^2+2pq+2q^2\right)+b\left(2pq+q^2\right), a\left(2pq+q^2\right)+b\left(p^2+q^2\right) \\
T^2\left(p,q\right) &= T\left(p^2+q^2, 2pq+q^2\right)
\end{aligned}
$$

```scheme
(define (fib n)
  (define (even? n) (= (remainder n 2) 0))
  (define (fib-iter a b p q count)
    (cond
      ((= count 0) b)
      ((even? count)
        (fib-iter
          a
          b
          (+ (* p p) (* q q))
          (+ (* 2 p q) (* q q))
          (/ count 2)))
      (else
        (fib-iter
          (+ (* b p) (* a q) (* a p))
          (+ (* b p) (* a q))
          p
          q
          (- count 1)))))
  (fib-iter 1 0 0 1 n))
(fib 35) ; ==> 9227465
```

### Exercise 1.20

```scheme
(define (gcd a b)
  (if (= b 0)
    a
    (gcd b (remainder a b))))

(gcd 206 40)
; for normal-order evaluation (18 remainder operations)
; (gcd 206 40)
; (if (= 40 0) 206 (gcd 40 (remainder 206 40)))
; (gcd 40 (remainder 206 40))
; (if (= (remainder 206 40) 0) 40 (gcd (remainder 206 40) (remainder 40 (remainder 206 40))))
; (if (= 6 0)  ; remainder +1
;   40
;   (gcd (remainder 206 40) (remainder 40 (remainder 206 40))))
; (gcd (remainder 206 40) (remainder 40 (remainder 206 40)))
; (if (= (remainder 40 (remainder 206 40)) 0)
;   (remainder 206 40)
;   (gcd
;     (remainder 40 (remainder 206 40))
;     (remainder (remainder 206 40) (remainder 40 (remainder 206 40)))))
; (if (= 4 0)  ; remainder +2
;   (remainder 206 40)
;   (gcd
;     (remainder 40 (remainder 206 40))
;     (remainder (remainder 206 40) (remainder 40 (remainder 206 40)))))
; (gcd
;   (remainder 40 (remainder 206 40))
;   (remainder (remainder 206 40) (remainder 40 (remainder 206 40))))
; (if (= (remainder (remainder 206 40) (remainder 40 (remainder 206 40))) 0)
;   (remainder 40 (remainder 206 40))
;   (gcd
;     (remainder (remainder 206 40) (remainder 40 (remainder 206 40)))
;     (remainder (remainder 40 (remainder 206 40)) (remainder (remainder 206 40) (remainder 40 (remainder 206 40))))))
; (if (= 2 0)  ; remainder +4
;   (remainder 40 (remainder 206 40))
;   (gcd
;     (remainder (remainder 206 40) (remainder 40 (remainder 206 40)))
;     (remainder (remainder 40 (remainder 206 40)) (remainder (remainder 206 40) (remainder 40 (remainder 206 40))))))
; (gcd
;   (remainder (remainder 206 40) (remainder 40 (remainder 206 40)))
;   (remainder (remainder 40 (remainder 206 40)) (remainder (remainder 206 40) (remainder 40 (remainder 206 40)))))
; (if (= (remainder (remainder 40 (remainder 206 40)) (remainder (remainder 206 40) (remainder 40 (remainder 206 40)))) 0)
;   (remainder (remainder 206 40) (remainder 40 (remainder 206 40)))
;   (gcd
;     (remainder (remainder 40 (remainder 206 40)) (remainder (remainder 206 40) (remainder 40 (remainder 206 40))))
;     (remainder (remainder (remainder 206 40) (remainder 40 (remainder 206 40))) (remainder (remainder 40 (remainder 206 40)) ; (remainder (remainder 206 40) (remainder 40 (remainder 206 40)))))))
; (if (= 0 0)  ; remainder +7
;   (remainder (remainder 206 40) (remainder 40 (remainder 206 40)))
;   (gcd
;     (remainder (remainder 40 (remainder 206 40)) (remainder (remainder 206 40) (remainder 40 (remainder 206 40))))
;     (remainder (remainder (remainder 206 40) (remainder 40 (remainder 206 40))) (remainder (remainder 40 (remainder 206 40)) (remainder (remainder 206 40) (remainder 40 (remainder 206 40)))))))
; (remainder (remainder 206 40) (remainder 40 (remainder 206 40)))
; ==> 2  ; remainder +4

; for applicative-order evaluation (4 remainder operations)
; (gcd 206 40)
; (if (= 40 0) 206 (gcd 40 (remainder 206 40)))
; (gcd 40 6)  ; remainder +1
; (if (= 6 0) 40 (gcd 6 (remainder 40 6)))
; (gcd 6 4)  ; remainder +1
; (if (= 4 0) 6 (gcd 4 (remainder 6 4)))
; (gcd 4 2)  ; remainder +1
; (if (= 2 0) 4 (gcd 2 (remainder 4 2)))
; (gcd 2 0)  ; remainder +1
; (if (= 0 0) 2 (gcd 2 (remainder 0 0)))
; ==> 2
```

### Exercise 1.21

```scheme
(define (smallest-divisor n)
  (define (divides? a b) (= (remainder b a) 0))
  (define (square n) (* n n))
  (define (find-divisor n test-divisor)
    (cond ((> (square test-divisor) n) n)
      ((divides? test-divisor n) test-divisor)
      (else (find-divisor n (+ test-divisor 1)))))

  (find-divisor n 2))
(smallest-divisor 199)
; (find-divisor 199 2)
; (find-divisor 199 3)
; ...
; (find-divisor 199 15)
; ==> 199
```

A similar event happens for 1999 where `find-diivisor` exhausts `test-divisor` from 2 to 45, and since the square of 45 is larger than 1999, it gives up and returns 1999. For 19999, when `test-divisor` becomes 7, `(divides? 7 19999)` returns `#t` and the iterative process stops and returns 7.

### Exercise 1.22

Because computing for primes larger than a million seems to be nearly instantaneous in modern hardware, I decided to increase their values by several orders of magnitude.

```scheme
; search-for-primes prints out `count` number of primes from (including) `from`.
; If `count` <= 0 terminate the search.
; If from <= 1 set from to 2
(define (search-for-primes from count)
  (define (even? n) (= (remainder n 2) 0))

  ; prime? checks for primality
  (define (prime? n)
    (define (smallest-divisor n)
      (define (divides? a b) (= (remainder b a) 0))

      (define (find-divisor n test-divisor)
        (cond ((> (square test-divisor) n) n)
          ((divides? test-divisor n) test-divisor)
          (else (find-divisor n (+ test-divisor 1)))))

      (find-divisor n 2))
    (= n (smallest-divisor n)))

  ; timed-prime? prints a message and returns true if n is prime; returns false otherwise
  (define (timed-prime? n)
    (define (start-prime-test n start-time)
      (if (prime? n)
        (report-prime (- (runtime) start-time))
        #f))

    (define (report-prime elapsed-time)
      (newline)
      (display n)
      (display " is a prime")
      (display " *** ")
      (display elapsed-time)
      #t)

    (start-prime-test n (runtime)))

  (define (search-for-primes-iter n c)
    (cond ((= c 0) 0)
      ((timed-prime? n) (search-for-primes-iter (+ n 2) (- c 1)))
      (else (search-for-primes-iter (+ n 2) c))))
  
  (cond
    ((<= count 0) 0)
    ((<= from 2) (search-for-primes-iter 3 (- count 1)))
    ((even? from) (search-for-primes-iter (+ from 1) count))
    (else (search-for-primes-iter from count))))

; increase by sqrt(10) per iteration
(search-for-primes 1000000000 3)
; 1000000007 is a prime *** .06
; 1000000009 is a prime *** .07
; 1000000021 is a prime *** .06

(search-for-primes 3162280000 3)
; 3162280001 is a prime *** .07999999999999996
; 3162280049 is a prime *** .07000000000000006
; 3162280063 is a prime *** .07999999999999996

(search-for-primes 10000000000 3)
; 10000000019 is a prime *** .1100000000000001
; 10000000033 is a prime *** .14
; 10000000061 is a prime *** .1299999999999999

(search-for-primes 31622800000 3)
; 31622800021 is a prime *** .21999999999999997
; 31622800031 is a prime *** .21999999999999997
; 31622800037 is a prime *** .2100000000000002

(search-for-primes 100000000000 3)
; 100000000003 is a prime *** .3999999999999997
; 100000000019 is a prime *** .3799999999999999
; 100000000057 is a prime *** .36999999999999966

(search-for-primes 316228000000 3)
; 316228000021 is a prime *** .6600000000000001
; 316228000051 is a prime *** .6699999999999999
; 316228000057 is a prime *** .6699999999999999

(search-for-primes 1000000000000 3)
; 1000000000039 is a prime *** 1.17
; 1000000000061 is a prime *** 1.17
; 1000000000063 is a prime *** 1.1900000000000004

(search-for-primes 3162280000000 3)
; 3162280000021 is a prime *** 2.1000000000000014
; 3162280000043 is a prime *** 2.41
; 3162280000109 is a prime *** 2.25

(search-for-primes 10000000000000 3)
; 10000000000037 is a prime *** 3.759999999999998
; 10000000000051 is a prime *** 3.75
; 10000000000099 is a prime *** 3.7600000000000016
```

Notice that when the numbers incrases by two orders of magnitude (every four iterations), the time it takes increases by one order of magnitude. That is, $T\left(100n\right) \approx 10T\left(n\right)$ This satisfies $\Theta\left(T\left(n\right)\right) = \Theta\left(\sqrt{n}\right)$.

### Exercise 1.23

The `prime?` function in the above code is replaced with as follows:

```scheme
(define (search-for-primes from count)
  ; ... code above goes here

  ; prime? checks for primality
  (define (prime? n)
    (define (smallest-divisor n)
      (define (divides? a b) (= (remainder b a) 0))

      (define (find-divisor n test-divisor)
        (define (next divisor)
          (if (= divisor 2) 3 (+ divisor 2)))
        (cond ((> (square test-divisor) n) n)
          ((divides? test-divisor n) test-divisor)
          (else (find-divisor n (next test-divisor)))))

      (find-divisor n 2))
    (= n (smallest-divisor n)))

; ... code below goes here
)
(search-for-primes 1000000000 3)
; 1000000007 is a prime *** 3.0000000000000027e-2
; 1000000009 is a prime *** .03999999999999998
; 1000000021 is a prime *** .02999999999999997

(search-for-primes 3162280000 3)
; 3162280001 is a prime *** 5.0000000000000044e-2
; 3162280049 is a prime *** .06
; 3162280063 is a prime *** 5.0000000000000044e-2

(search-for-primes 10000000000 3)
; 10000000019 is a prime *** .10000000000000009
; 10000000033 is a prime *** .08999999999999997
; 10000000061 is a prime *** .09999999999999998

(search-for-primes 31622800000 3)
; 31622800021 is a prime *** .15000000000000002
; 31622800031 is a prime *** .16999999999999993
; 31622800037 is a prime *** .21999999999999997

(search-for-primes 100000000000 3)
; 100000000003 is a prime *** .28
; 100000000019 is a prime *** .28
; 100000000057 is a prime *** .2599999999999998

(search-for-primes 316228000000 3)
; 316228000021 is a prime *** .46999999999999975
; 316228000051 is a prime *** .45999999999999996
; 316228000057 is a prime *** .46999999999999975

(search-for-primes 1000000000000 3)
; 1000000000039 is a prime *** .81
; 1000000000061 is a prime *** .8399999999999999
; 1000000000063 is a prime *** .8399999999999999

(search-for-primes 3162280000000 3)
; 3162280000021 is a prime *** 1.490000000000001
; 3162280000043 is a prime *** 1.5500000000000007
; 3162280000109 is a prime *** 1.4700000000000006

(search-for-primes 10000000000000 3)
; 10000000000037 is a prime *** 2.7299999999999986
; 10000000000051 is a prime *** 2.6799999999999997
; 10000000000099 is a prime *** 3.0100000000000016
```

Using linear regression, we can say that the time it takes for primes to be evaluated is roughly 73% of the original time. Removing even numbers as candidate divisors reduced the amount of time to compute by 27%. This is different from the 50% reduction that would have been expected by removing 50% of the candidate divisors.

This is perhaps attributed to the time it takes for `next` to be evaluated, and the `if` function inside it.

### Exercise 1.24

```scheme
(define (search-for-primes from count)
  ; ... code above goes here

  ; fast-prime? checks for primality using Fermat's little theorem
  (define (fast-prime? n times)
    (define (fermat-test n)
      (define (try-it a) (= (expmod a n n) a))
      (try-it (+ 1 (random (- n 1)))))
    (cond ((= times 0) true)
      ((fermat-test n) (fast-prime? n (- times 1)))
      (else false)))

  ; timed-prime? prints a message and returns true if n is prime according to fast-prime; returns false otherwise
  (define (timed-prime? n)
    (define (start-prime-test n start-time)
      (if (fast-prime? n 100)
        (report-prime (- (runtime) start-time))
        #f))

    (define (report-prime elapsed-time)
      (newline)
      (display n)
      (display " is a prime")
      (display " *** ")
      (display elapsed-time)
      #t)

    (start-prime-test n (runtime)))

; ... code below goes here
)
; incrase by sqrt(10) per iteration
(search-for-primes 1000000000 3)
; 1000000007 is a prime *** 1.0000000000000009e-2
; 1000000009 is a prime *** 1.0000000000000009e-2
; 1000000021 is a prime *** 1.0000000000000009e-2

(search-for-primes 3162280000 3)
; 3162280001 is a prime *** 9.999999999999953e-3
; 3162280049 is a prime *** 1.0000000000000009e-2
; 3162280063 is a prime *** 1.0000000000000009e-2

(search-for-primes 10000000000 3)
; 10000000019 is a prime *** 1.0000000000000009e-2
; 10000000033 is a prime *** 1.9999999999999962e-2
; 10000000061 is a prime *** 2.0000000000000018e-2

(search-for-primes 31622800000 3)
; 31622800021 is a prime *** 2.0000000000000018e-2
; 31622800031 is a prime *** 1.0000000000000009e-2
; 31622800037 is a prime *** 1.9999999999999962e-2

(search-for-primes 100000000000 3)
; 100000000003 is a prime *** 1.0000000000000009e-2
; 100000000019 is a prime *** 1.0000000000000009e-2
; 100000000057 is a prime *** 1.0000000000000009e-2

(search-for-primes 316228000000 3)
; 316228000021 is a prime *** 1.9999999999999962e-2
; 316228000051 is a prime *** 1.0000000000000009e-2
; 316228000057 is a prime *** 2.0000000000000018e-2

(search-for-primes 1000000000000 3)
; 1000000000039 is a prime *** 0.
; 1000000000061 is a prime *** 1.0000000000000009e-2
; 1000000000063 is a prime *** 1.0000000000000009e-2

(search-for-primes 3162280000000 3)
; 3162280000021 is a prime *** 1.9999999999999907e-2
; 3162280000043 is a prime *** 1.0000000000000009e-2
; 3162280000109 is a prime *** 3.0000000000000027e-2

(search-for-primes 10000000000000 3)
; 10000000000037 is a prime *** 1.0000000000000009e-2
; 10000000000051 is a prime *** 2.0000000000000018e-2
; 10000000000099 is a prime *** 1.0000000000000009e-2
```

Computing for prime numbers feels nearly instantaneous. Much, much larger numbers may need to be used here.

```scheme
(search-for-primes 1000000000000000000000000000 3)
; 1000000000000000000000000103 is a prime *** .02999999999999997
; 1000000000000000000000000279 is a prime *** 1.9999999999999962e-2
; 1000000000000000000000000283 is a prime *** 3.0000000000000027e-2

(search-for-primes 1000000000000000000000000000000000000000000000000000000 3)
; 1000000000000000000000000000000000000000000000000000031 is a prime *** .07999999999999996
; 1000000000000000000000000000000000000000000000000000157 is a prime *** 5.0000000000000044e-2
; 1000000000000000000000000000000000000000000000000000169 is a prime *** .07000000000000006

(search-for-primes 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 3)
; 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000019 is a prime *** .16999999999999993
; 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001141 is a prime *** .1399999999999999
; 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001207 is a prime *** .1399999999999999

(search-for-primes 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 3)
; 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000499 is a prime *** .43999999999999995
; 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001107 is a prime *** .4500000000000002
; 1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001591 is a prime *** .4500000000000002
```

After each iteration the base is squared, leading to a near tripling of checking time: $T\left(n^2\right) \approx 3T\left(n\right)$. This satisfies $\Theta\left(T\left(n\right)\right)=\Theta\left(\log n\right)$.

### Exercise 1.25

The original procedure is as follows:

```scheme
(define (expmod base exp m)
  (define (square x) (* x x))
  (cond ((= exp 0) 1)
    ((even? exp) (remainder (square (expmod base (/ exp 2) m)) m))
    (else (remainder (* base (expmod base (- exp 1) m)) m))))
```

and the modified is as follows:

```scheme
(define (expmod base exp m)
  (remainder (fast-expt base exp) m))
```

The issue here is that `(fast-expt ...)` has to be evaluated first, and `base` and `exp` can be ridiculously high. After all of that, its remainder when divided by `m` is computed, and all that computational power might have been wasted.

The original keeps the working value no more than `m`, and this is indicated by the `remainder` operation after every step.

### Exercise 1.26

> "...you have transformed the $\Theta\left(\log n\right)$ process into a $\Theta\left(n\right)$ process."

Consider first why the `square` procedure is being used. This is to avoid computing the value twice, as `(expmod base (/ exp 2) m)` would have already been evaluated and stored somewhere, and what is left to be done is to multiply its value by itself.

By using `(* (expmod base (/ exp 2) m) (expmod base (/ exp 2) m))`, computation would be done *twice* every recursive call. By doubling `exp`, the number of calls it takes to compute will then double, compared to just increasing by one if `square` were used.

This can be proven using induction. Suppose that `expmod` takes $T\left(n\right)$ time to compute where $n$ is our `exp`. If we double `exp`, the time it takes for the `(remainder (* ...))` code to run will be $2T\left(n\right)$, since each `expmod` call takes $T\left(n\right)$. Because of this linear relationship, $\Theta\left(T\left(n\right)\right)=\Theta\left(n\right)$

### Exercise 1.27

```scheme
(define (test-camichael n)
  (define (expmod base exp m)
    (define (even? n) (= (remainder n 2) 0))
    (define (square x) (* x x))
    (cond
      ((= exp 0) 1)
      ((even? exp) (remainder (square (expmod base (/ exp 2) m)) m))
      (else (remainder (* base (expmod base (- exp 1) m)) m))))
  ; test-camichael-recursive tests for every a < n. Once `a` reaches `n` return true.
  (define (test-camichael-recursive a n)
    (cond
      ((= a n) #t)
      ((not (= (expmod a n n) a)) #f)
      (else (test-camichael-recursive (+ a 1) n))))
  (test-camichael-recursive 2 n))
(test-camichael 561)   ; ==> #t
(test-camichael 1105)  ; ==> #t
(test-camichael 1729)  ; ==> #t
(test-camichael 2465)  ; ==> #t
(test-camichael 2821)  ; ==> #t
(test-camichael 6601)  ; ==> #t
```

### Exercise 1.28

```scheme
; miller-rabin checks if n is prime
(define (miller-rabin n)
  ; expmod is special.
  ; It returns 0 if it detects a "nontrivial square root of 1 mod n"
  (define (expmod base exp m)
    (define (special-case n)
      ; if-nsr-then-zero checks if n is a non-trivial square root of 1 mod m and returns zero if so
      (define (if-nsr-then-zero n sq)
        (define (neq a b) (not (= a b)))
        (if (and (neq n 1) (neq n (- m 1)) (= sq 1)) 0 sq))
      (if-nsr-then-zero n (remainder (square n) m)))
    (define (even? n) (= (remainder n 2) 0))
    (define (square n) (* n n))
    (cond
      ((= exp 0) 1)
      ((even? exp) (special-case (expmod base (/ exp 2) m)))
      (else (remainder (* base (expmod base (- exp 1) m)) m))))
  
  (define (test n)
    (define (try-it a)
      (= (expmod a (- n 1) n) 1))
    (try-it (+ 1 (random (- n 1)))))
  (define (test-times times)
    (cond ((= times 0) #t)
      ((test n) (test-times (- times 1)))
      (else #f)))
  (test-times 3))

; non-primes
(miller-rabin 2821) ; ==> #f
(miller-rabin 1105) ; ==> #f
(miller-rabin 1729) ; ==> #f
(miller-rabin 2465) ; ==> #f
(miller-rabin 2821) ; ==> #f
(miller-rabin 6601) ; ==> #f

; primes
(miller-rabin 3162280000021) ; ==> #t
(miller-rabin 3162280000043) ; ==> #t
(miller-rabin 3162280000109) ; ==> #t
```

## 1.3 Formulating Abstractions with Higher-Order Procedures

### Exercise 1.29

```scheme
; simpson performs a Simpson's Rule integration of f from a to b.
; n denotes accuracy (and is implicitly turned even)
(define (simpson f a b n)
  (define m (if (= 1 (remainder n 2)) (+ n 1) n)) ; "new n"
  (define h (/ (- b a) n))  ; we'll turn it into a floating-point later
  (define (y k) (f (+ a (* k h))))
  (define (add-two x) (+ x 2))
  (* (/ h 3.0)
    (+ (y 0)
      (y n)
      (* 4 (sum y 1 add-two (- m 1)))
      (* 2 (sum y 2 add-two (- m 2))))))
(simpson cube 0 1 1000) ; ==> 0.25
```

### Exercise 1.30

```scheme
(define (sum term a next b)
  (define (iter a result)
    (if (> a b)
      result
      (iter (next a) (+ result (term a)))))
  (iter a 0))
```

### Exercise 1.31

```scheme
(define (product term a next b)
  (if (> a b)
    1
    (* (term a) (product term (next a) next b))))
; approx-pi evaluates pi to some accuracy level n
(define (approx-pi n)
  (define (inc n) (+ n 1))
  ; term n is as follows: (term 1) = 2/3; (term 2) = 4/3; (term 3) = 4/5; ...
  (define (term n)
    (define numerator (+ 2.0 (- n (remainder n 2))))
    (define denominator (+ 2.0 (- n (remainder (+ n 1) 2))))
    (/ numerator denominator))
  (* 4.0 (product term 1 inc n)))
(approx-pi 10000) ; ==> 3.1417497057379635 (not a very good job at approximating now huh)
```

Similarly, an iterative solution can be used:

```scheme
(define (product term a next b)
  (define (iter a result)
    (if (> a b)
      result
      (iter (next a) (* result (term a)))))
  (iter a 1))
(approx-pi 10000) ; ==> 3.1417497057380084
```

### Exercise 1.32

```scheme
(define (accumulate combiner null-value term a next b)
  (if (> a b)
    null-value
    (combiner (term a) (accumulate combiner null-value term (next a) next b))))
(define (sum term a next b) (accumulate + 0 term a next b))
(define (product term a next b) (accumulate * 1 term a next b))
```

Similarly, an iterative solution can be used:

```scheme
(define (accumulate combiner null-value term a next b)
  (define (iter a result)
    (if (> a b)
      result
      (iter (next a) (combiner result (term a)))))
  (iter a null-value))
```

### Exercise 1.33

```scheme
; filtered-accumulate accumulates term(i) from a to b inclusive that satisfy filter(i)
(define (filtered-accumulate combiner null-value term a next b filter)
  (define (iter a result)
    (cond
      ((> a b) result)
      ((filter a) (iter (next a) (combiner result (term a))))
      (else (iter (next a) result))))
  (iter a null-value))

; sum-of-square-of-primes computes sum of square of primes from a to b inclusive
(define (sum-of-square-of-primes a b)
  (define (square n) (* n n))
  (define (inc n) (+ n 1))
  (define (prime? n)
    (define (smallest-divisor n)
      (define (divides? a b) (= (remainder b a) 0))

      (define (find-divisor n test-divisor)
        (cond ((> (square test-divisor) n) n)
          ((divides? test-divisor n) test-divisor)
          (else (find-divisor n (+ test-divisor 1)))))
      
      (find-divisor n 2))
    (if (< n 2) #f (= n (smallest-divisor n)))) ; disclude <= 2
  (filtered-accumulate + 0 square a inc b prime?))
(sum-of-square-of-primes 1 10) ; ==> 4+9+25+49 = 87

; product-of-relative-primes returns the product of i from 1 to n where gcd(i,n) == 1
(define (product-of-relative-primes n)
  (define (gcd a b)
    (if (= b 0)
      a
      (gcd b (remainder a b))))
  (define (is-relatively-prime x) (= (gcd x n) 1))
  (define (identity x) x)
  (define (inc x) (+ x 1))
  (filtered-accumulate * 1 identity 1 inc n is-relatively-prime))
(product-of-relative-primes 10) ; ==> 1*3*7*9 = 189
```

### Exercise 1.34

```scheme
(define (f g) (g 2))
(f square) ; ==> (square 2) = 4
(f (lambda (z) (* z (+ z 1)))) ; ==> (* 2 (+ 2 1)) = 6

(f f)
; (f 2)
; (2 2)
```

But since `2` is not a callable function, the interpreter outputs an error.

```scheme
;The object 2 is not applicable.
;To continue, call RESTART with an option number:
; (RESTART 2) => Specify a procedure to use in its place.
; (RESTART 1) => Return to read-eval-print level 1.
```

### Exercise 1.35

Note that the fixed point for $f\left(x\right)=1+\frac{1}{x}$ solves the equation $x=1+\frac{1}{x}$, which can be rewritten to $x^2-x-1=0$. Solving the quadratic equation leads $x=\frac{1\pm\sqrt{5}}{2}$. This means that $\phi=\frac{1+\sqrt{5}}{2}$ is *a*, but not the only, fixed point for the transformation.

Let us then write a procedure to evaluate $\phi$ using `fixed-point`.

```scheme
(fixed-point (lambda (x) (+ 1 (/ 1 x))) 1.0) ; ==> 1.618...
```

### Exercise 1.36

```scheme
(define (fixed-point f first-guess)
  (define (close-enough x y) (< (abs (- x y)) 0.00001))
  ; print-approx just prints out x and a newline
  (define (print-approx x)
    (newline)
    (display "Checking ")
    (display x))
  (define (try guess)
    (let ((next (f guess)))
      (print-approx guess)
      (if (close-enough guess next)
        next
        (try next))))
  (try first-guess))
(fixed-point (lambda (x) (/ (log 1000) (log x))) 3)
; Checking 3
; Checking 6.287709822868153
; Checking 3.757079790200296
; Checking 5.218748919675315
; Checking 4.180797746063314
; Checking 4.828902657081293
; Checking 4.386936895811029
; Checking 4.671722808746095
; Checking 4.481109436117821
; Checking 4.605567315585735
; Checking 4.522955348093164
; Checking 4.577201597629606
; Checking 4.541325786357399
; Checking 4.564940905198754
; Checking 4.549347961475409
; Checking 4.5596228442307565
; Checking 4.552843114094703
; Checking 4.55731263660315
; Checking 4.554364381825887
; Checking 4.556308401465587
; Checking 4.555026226620339
; Checking 4.55587174038325
; Checking 4.555314115211184
; Checking 4.555681847896976
; Checking 4.555439330395129
; Checking 4.555599264136406
; Checking 4.555493789937456
; Checking 4.555563347820309
; Checking 4.555517475527901
; Checking 4.555547727376273
; Checking 4.555527776815261
; Checking 4.555540933824255
; ==> 4.555532257016376
```

### Exercise 1.37

```scheme
; const-frac evaluates the k-term finite continued fraction
; where n(i), d(i) are terms where i is from 1 to k.
(define (const-frac n d k)
  (define (const-frac-iter i)
    (if (> i k)
      0
      (/ (n i) (+ (d i) (const-frac-iter (+ i 1))))))
  (const-frac-iter 1))
; silver-ratio returns the silver ratio (0.61803..) using const-frac with k iterations
(define (silver-ratio k)
  (const-frac (lambda (i) 1.0) (lambda (i) 1.0) k))
(silver-ratio 1)  ; ==> 1.0
(silver-ratio 2)  ; ==> 0.5
(silver-ratio 3)  ; ==> 0.6667
(silver-ratio 4)  ; ==> 0.6000
(silver-ratio 5)  ; ==> 0.625
(silver-ratio 10) ; ==> 0.6179775280898876
(silver-ratio 15) ; ==> 0.6180344478216819
(silver-ratio 20) ; ==> 0.6180339850173578
(silver-ratio 25) ; ==> 0.6180339887802426
(silver-ratio 50) ; ==> 0.6180339887498948
```

Similarly, an iterative solution can be written:

```scheme
(define (const-frac n d k)
  ; i counts BACKWARDS!
  (define (const-frac-iter i result)
    (if (= i 0)
      result
      (const-frac-iter (- i 1) (/ (n i) (+ (d i) result)))))
  (const-frac-iter k 0))
(silver-ratio 1)  ; ==> 1.0
(silver-ratio 2)  ; ==> 0.5
(silver-ratio 3)  ; ==> 0.6666666666666666
(silver-ratio 4)  ; ==> 0.6000000000000001
(silver-ratio 5)  ; ==> 0.625
(silver-ratio 10) ; ==> 0.6179775280898876
(silver-ratio 15) ; ==> 0.6180344478216819
(silver-ratio 20) ; ==> 0.6180339850173578
(silver-ratio 25) ; ==> 0.6180339887802426
(silver-ratio 50) ; ==> 0.6180339887498948
```

The result becomes accurate to four decimal places by `k=10`.

### Exercise 1.38

```scheme
; approx-e-less-2 computes the approximation of e-2
; using Euler's continued fraction and const-frac.
; k is the number of iterations to be done
(define (approx-e-less-2 k)
  (define (N i)
    1.0)
  (define (D i)
    (if (= 2 (remainder i 3))
      (* (/ (+ i 1) 3) 2)
      1))
  (const-frac N D k))
(approx-e-less-2 10) ; ==> 0.7182817182817183
```

### Exercise 1.39

```scheme
; tan-cf computes the tangent of x (radians) using const-frac.
; Note that k might have to be large if x were large.
(define (tan-cf x k)
  (define (N i)
    (if (= i 1)
      x
      (- (* x x))))
  (define (D i)
    (- (* 2 i) 1.0))
  (const-frac N D k))
(tan 3)       ; ==> -.1425465430742778
(tan-cf 3 10) ; ==> -.1425465438397583
```

### Exercise 1.40

This is trivial to implement.

```scheme
; cubic represents a cubic equation x^3+ax^2+bx+c
(define (cubic a b c)
  (lambda (x) (+ (* x x x) (* a x x) (* b x) c)))
```

### Exercise 1.41

This is also trivial to implement but somehow difficult to wrap around.

```scheme
; double returns a wrapped function such that f -> f(f) where f : val -> val
(define (double f) (lambda (x) (f (f x))))
(define (inc x) (+ x 1))
(((double (double double)) inc) 5) 
; (((double (lambda (f) (double (double f)))) inc) 5) ; substitute the parent double
; (((lambda (f) (double (double (double (double f))))) inc) 5)
; ((double (double (double (double inc)))) 5)
; ((double (double (double (lambda (x) (inc (inc x)))))) 5)
; ((double (double (lambda (x) (inc (inc (inc (inc x))))))) 5)
; ((double (lambda (x) (inc (inc (inc (inc (inc (inc (inc (inc x)))))))))) 5)
; ((lambda (x) (inc (inc (inc (inc (inc (inc (inc (inc (inc (inc (inc (inc (inc (inc (inc (inc x))))))))))))))))) 5)
; (inc (inc (inc (inc (inc (inc (inc (inc (inc (inc (inc (inc (inc (inc (inc (inc 5))))))))))))))))
; ==> 21
```

### Exercise 1.42

```scheme
(define (compose f g)
  (lambda (x) (f (g x))))
((compose square inc) 6) ; ==> 49
```

### Exercise 1.43

```scheme
(define (repeated f n)
  (define (iter i)
    (if (= i n)
      (lambda (x) x)
      (compose f (iter (+ i 1)))))
  (iter 0))
((repeated square 2) 5) ; ==> 625
```

As always, an iterative solution can be found:

```scheme
(define (repeated f n)
  (define (iter result i)
    (if (= i n)
      result
      (iter (compose f result) (+ i 1))))
  (iter f 1))
((repeated square 2) 5) ; ==> 625
```

### Exercise 1.44

```scheme
; smooth returns a procedure describing a smoothed function
(define (smooth f)
  (lambda (x)
    (+ (f (- x dx))
      (f x)
      (f (+ x dx)))))

; smooth-n returns the n-fold smoothed function
(define (smooth-n f n)
  (repeated smooth n))
```

### Exercise 1.45

```scheme
; n-th root returns a function for the n'th root of x such that
; the fixed point of y -> x/y^(n-1) is calculated, and the transformation is done r times.
(define (nth-root n r)
  (define (average a b) (/ (+ a b) 2.0))
  (lambda (x)
    (define (ave-dump y) (average y (/ x (expt y (- n 1)))))
    (fixed-point (repeated ave-dump r) 1.0)))
((nth-root 2 1) 4) ; ==> 2.000000000000002
```

It does not seem to work for degree 6 or higher. Maybe I'm doing something wrong here.
