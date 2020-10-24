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
