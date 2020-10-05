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
