(set-info :smt-lib-version 2.6)
(set-logic QF_NRA)
(set-info :source |
Generated by: Anastasiia Izycheva, Eva Darulova
Generated on: 2020-09-11
Generator: Pine (using Z3 Python API)
Application: Check inductiveness of a loop invariant
Target solver: Z3

These benchmarks were generated while developing the tool Pine [1], which uses
CVC4/Z3 to check inductiveness of invariants. The work is described in [2].

[1] https://github.com/izycheva/pine
[2] A.Izycheva, E.Darulova, H.Seidl, SAS'20, "Counterexample- and Simulation-Guided Floating-Point Loop Invariant Synthesis"

 Loop:
   u' := u + 0.01 * v
   v' := v + 0.01 * (-0.5 * v - 9.81 * u)

 Input ranges:
   u in [0.0,0.0]
   v in [2.0,3.0]

 Invariant:
   -1.0*u + 0.24*v + 0.87*u^2 + -0.12*u*v + 0.07*v^2 <= 1.43
 and
   u in [-0.7,2.0]
   v in [-6.3,3.0]

 Query: Loop and Invariant and not Invariant'
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "industrial")
(set-info :status unknown)
(declare-fun u! () Real)
(declare-fun v! () Real)
(declare-fun u () Real)
(declare-fun v () Real)
(assert
 (let ((?x246 (+ (* (* (- (/ 3.0 25.0)) u!) v!) (+ (* (* (/ 7.0 100.0) v!) v!) (* (- 1.0) u!)))))
 (let (($x69 (and (<= (- (/ 7.0 10.0)) u!) (>= 2.0 u!) (<= (- (/ 63.0 10.0)) v!) (>= 3.0 v!))))
 (let (($x135 (and $x69 (>= (/ 143.0 100.0) (+ (* (/ 6.0 25.0) v!) (+ (* (* (/ 87.0 100.0) u!) u!) ?x246))) )))
 (let (($x60 (and (= u! (+ u (* (/ 1.0 100.0) v))) (= v! (+ v (* (/ 1.0 100.0) (- (* (- (/ 1.0 2.0)) v) (* (/ 981.0 100.0) u))))))))
 (let ((?x258 (+ (* (* (- (/ 3.0 25.0)) u) v) (+ (* (* (/ 7.0 100.0) v) v) (* (- 1.0) u)))))
 (let (($x129 (>= 3.0 v)))
 (let (($x271 (and (and (<= (- (/ 7.0 10.0)) u) (>= 2.0 u) (<= (- (/ 63.0 10.0)) v) $x129) (>= (/ 143.0 100.0) (+ (* (/ 6.0 25.0) v) (+ (* (* (/ 87.0 100.0) u) u) ?x258))) )))
 (and $x271 $x60 (not $x135))))))))))
(check-sat)
(exit)