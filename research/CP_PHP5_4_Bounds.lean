import PEqualNP.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/- Research checkpoint for L-meta-9698.
Verified bounds: every refutation has at least 90 lines; a 109-line refutation exists.
The assigned cutoff of 108 lines remains open. This file contains supporting results.
-/

namespace PEqualNP.Outside.L_meta_9698

open PEqualNP.Search PEqualNP.ProofComplexity

abbrev V := Fin 5 × Fin 4

abbrev formula : Set (Clause V) := PHP 5 4

def c0 : Clause V := {((0, 0), false), ((1, 0), false)}

def e0 : CPLine V := clauseCP c0

def p0 : List (CPLine V) := e0 :: []

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d0 : IsCPDerivation formula p0 :=
  IsCPDerivation.ax c0 IsCPDerivation.nil (Or.inr ⟨0, 1, 0, by decide, rfl⟩)

def c1 : Clause V := {((0, 0), false), ((2, 0), false)}

def e1 : CPLine V := clauseCP c1

def p1 : List (CPLine V) := e1 :: p0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d1 : IsCPDerivation formula p1 :=
  IsCPDerivation.ax c1 d0 (Or.inr ⟨0, 2, 0, by decide, rfl⟩)

def c2 : Clause V := {((0, 0), false), ((3, 0), false)}

def e2 : CPLine V := clauseCP c2

def p2 : List (CPLine V) := e2 :: p1

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d2 : IsCPDerivation formula p2 :=
  IsCPDerivation.ax c2 d1 (Or.inr ⟨0, 3, 0, by decide, rfl⟩)

def c3 : Clause V := {((0, 0), false), ((4, 0), false)}

def e3 : CPLine V := clauseCP c3

def p3 : List (CPLine V) := e3 :: p2

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d3 : IsCPDerivation formula p3 :=
  IsCPDerivation.ax c3 d2 (Or.inr ⟨0, 4, 0, by decide, rfl⟩)

def c4 : Clause V := {((1, 0), false), ((2, 0), false)}

def e4 : CPLine V := clauseCP c4

def p4 : List (CPLine V) := e4 :: p3

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d4 : IsCPDerivation formula p4 :=
  IsCPDerivation.ax c4 d3 (Or.inr ⟨1, 2, 0, by decide, rfl⟩)

def c5 : Clause V := {((1, 0), false), ((3, 0), false)}

def e5 : CPLine V := clauseCP c5

def p5 : List (CPLine V) := e5 :: p4

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d5 : IsCPDerivation formula p5 :=
  IsCPDerivation.ax c5 d4 (Or.inr ⟨1, 3, 0, by decide, rfl⟩)

def c6 : Clause V := {((1, 0), false), ((4, 0), false)}

def e6 : CPLine V := clauseCP c6

def p6 : List (CPLine V) := e6 :: p5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d6 : IsCPDerivation formula p6 :=
  IsCPDerivation.ax c6 d5 (Or.inr ⟨1, 4, 0, by decide, rfl⟩)

def c7 : Clause V := {((2, 0), false), ((3, 0), false)}

def e7 : CPLine V := clauseCP c7

def p7 : List (CPLine V) := e7 :: p6

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d7 : IsCPDerivation formula p7 :=
  IsCPDerivation.ax c7 d6 (Or.inr ⟨2, 3, 0, by decide, rfl⟩)

def c8 : Clause V := {((2, 0), false), ((4, 0), false)}

def e8 : CPLine V := clauseCP c8

def p8 : List (CPLine V) := e8 :: p7

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d8 : IsCPDerivation formula p8 :=
  IsCPDerivation.ax c8 d7 (Or.inr ⟨2, 4, 0, by decide, rfl⟩)

def c9 : Clause V := {((3, 0), false), ((4, 0), false)}

def e9 : CPLine V := clauseCP c9

def p9 : List (CPLine V) := e9 :: p8

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d9 : IsCPDerivation formula p9 :=
  IsCPDerivation.ax c9 d8 (Or.inr ⟨3, 4, 0, by decide, rfl⟩)

def e10 : CPLine V := (e1.1 + e4.1, e1.2 + e4.2)

def p10 : List (CPLine V) := e10 :: p9

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d10 : IsCPDerivation formula p10 :=
  IsCPDerivation.add d9 (List.mem_cons_of_mem e9 (List.mem_cons_of_mem e8 (List.mem_cons_of_mem e7 (List.mem_cons_of_mem e6 (List.mem_cons_of_mem e5 (List.mem_cons_of_mem e4 (List.mem_cons_of_mem e3 (List.mem_cons_of_mem e2 List.mem_cons_self)))))))) (List.mem_cons_of_mem e9 (List.mem_cons_of_mem e8 (List.mem_cons_of_mem e7 (List.mem_cons_of_mem e6 (List.mem_cons_of_mem e5 List.mem_cons_self)))))

def e11 : CPLine V := (e0.1 + e10.1, e0.2 + e10.2)

def p11 : List (CPLine V) := e11 :: p10

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d11 : IsCPDerivation formula p11 :=
  IsCPDerivation.add d10 (List.mem_cons_of_mem e10 (List.mem_cons_of_mem e9 (List.mem_cons_of_mem e8 (List.mem_cons_of_mem e7 (List.mem_cons_of_mem e6 (List.mem_cons_of_mem e5 (List.mem_cons_of_mem e4 (List.mem_cons_of_mem e3 (List.mem_cons_of_mem e2 (List.mem_cons_of_mem e1 List.mem_cons_self)))))))))) List.mem_cons_self

def e12 : CPLine V := (fun v => e11.1 v / (2 : ℤ), -((-e11.2) / (2 : ℤ)))

def p12 : List (CPLine V) := e12 :: p11

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d12 : IsCPDerivation formula p12 :=
  IsCPDerivation.div 2 d11 List.mem_cons_self (by decide) (by decide)

def e13 : CPLine V := (e2.1 + e5.1, e2.2 + e5.2)

def p13 : List (CPLine V) := e13 :: p12

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d13 : IsCPDerivation formula p13 :=
  IsCPDerivation.add d12 (List.mem_cons_of_mem e12 (List.mem_cons_of_mem e11 (List.mem_cons_of_mem e10 (List.mem_cons_of_mem e9 (List.mem_cons_of_mem e8 (List.mem_cons_of_mem e7 (List.mem_cons_of_mem e6 (List.mem_cons_of_mem e5 (List.mem_cons_of_mem e4 (List.mem_cons_of_mem e3 List.mem_cons_self)))))))))) (List.mem_cons_of_mem e12 (List.mem_cons_of_mem e11 (List.mem_cons_of_mem e10 (List.mem_cons_of_mem e9 (List.mem_cons_of_mem e8 (List.mem_cons_of_mem e7 (List.mem_cons_of_mem e6 List.mem_cons_self)))))))

def e14 : CPLine V := (e13.1 + e7.1, e13.2 + e7.2)

def p14 : List (CPLine V) := e14 :: p13

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d14 : IsCPDerivation formula p14 :=
  IsCPDerivation.add d13 List.mem_cons_self (List.mem_cons_of_mem e13 (List.mem_cons_of_mem e12 (List.mem_cons_of_mem e11 (List.mem_cons_of_mem e10 (List.mem_cons_of_mem e9 (List.mem_cons_of_mem e8 List.mem_cons_self))))))

def e15 : CPLine V := ((2 : ℤ) • e12.1, (2 : ℤ) * e12.2)

def p15 : List (CPLine V) := e15 :: p14

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d15 : IsCPDerivation formula p15 :=
  IsCPDerivation.mul 2 d14 (List.mem_cons_of_mem e14 (List.mem_cons_of_mem e13 List.mem_cons_self))

def e16 : CPLine V := (e15.1 + e14.1, e15.2 + e14.2)

def p16 : List (CPLine V) := e16 :: p15

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d16 : IsCPDerivation formula p16 :=
  IsCPDerivation.add d15 List.mem_cons_self (List.mem_cons_of_mem e15 List.mem_cons_self)

def e17 : CPLine V := (fun v => e16.1 v / (3 : ℤ), -((-e16.2) / (3 : ℤ)))

def p17 : List (CPLine V) := e17 :: p16

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d17 : IsCPDerivation formula p17 :=
  IsCPDerivation.div 3 d16 List.mem_cons_self (by decide) (by decide)

def e18 : CPLine V := (e3.1 + e6.1, e3.2 + e6.2)

def p18 : List (CPLine V) := e18 :: p17

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d18 : IsCPDerivation formula p18 :=
  IsCPDerivation.add d17 (List.mem_cons_of_mem e17 (List.mem_cons_of_mem e16 (List.mem_cons_of_mem e15 (List.mem_cons_of_mem e14 (List.mem_cons_of_mem e13 (List.mem_cons_of_mem e12 (List.mem_cons_of_mem e11 (List.mem_cons_of_mem e10 (List.mem_cons_of_mem e9 (List.mem_cons_of_mem e8 (List.mem_cons_of_mem e7 (List.mem_cons_of_mem e6 (List.mem_cons_of_mem e5 (List.mem_cons_of_mem e4 List.mem_cons_self)))))))))))))) (List.mem_cons_of_mem e17 (List.mem_cons_of_mem e16 (List.mem_cons_of_mem e15 (List.mem_cons_of_mem e14 (List.mem_cons_of_mem e13 (List.mem_cons_of_mem e12 (List.mem_cons_of_mem e11 (List.mem_cons_of_mem e10 (List.mem_cons_of_mem e9 (List.mem_cons_of_mem e8 (List.mem_cons_of_mem e7 List.mem_cons_self)))))))))))

def e19 : CPLine V := (e18.1 + e8.1, e18.2 + e8.2)

def p19 : List (CPLine V) := e19 :: p18

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d19 : IsCPDerivation formula p19 :=
  IsCPDerivation.add d18 List.mem_cons_self (List.mem_cons_of_mem e18 (List.mem_cons_of_mem e17 (List.mem_cons_of_mem e16 (List.mem_cons_of_mem e15 (List.mem_cons_of_mem e14 (List.mem_cons_of_mem e13 (List.mem_cons_of_mem e12 (List.mem_cons_of_mem e11 (List.mem_cons_of_mem e10 (List.mem_cons_of_mem e9 List.mem_cons_self))))))))))

def e20 : CPLine V := (e19.1 + e9.1, e19.2 + e9.2)

def p20 : List (CPLine V) := e20 :: p19

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d20 : IsCPDerivation formula p20 :=
  IsCPDerivation.add d19 List.mem_cons_self (List.mem_cons_of_mem e19 (List.mem_cons_of_mem e18 (List.mem_cons_of_mem e17 (List.mem_cons_of_mem e16 (List.mem_cons_of_mem e15 (List.mem_cons_of_mem e14 (List.mem_cons_of_mem e13 (List.mem_cons_of_mem e12 (List.mem_cons_of_mem e11 (List.mem_cons_of_mem e10 List.mem_cons_self))))))))))

def e21 : CPLine V := ((3 : ℤ) • e17.1, (3 : ℤ) * e17.2)

def p21 : List (CPLine V) := e21 :: p20

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d21 : IsCPDerivation formula p21 :=
  IsCPDerivation.mul 3 d20 (List.mem_cons_of_mem e20 (List.mem_cons_of_mem e19 (List.mem_cons_of_mem e18 List.mem_cons_self)))

def e22 : CPLine V := (e21.1 + e20.1, e21.2 + e20.2)

def p22 : List (CPLine V) := e22 :: p21

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d22 : IsCPDerivation formula p22 :=
  IsCPDerivation.add d21 List.mem_cons_self (List.mem_cons_of_mem e21 List.mem_cons_self)

def e23 : CPLine V := (fun v => e22.1 v / (4 : ℤ), -((-e22.2) / (4 : ℤ)))

def p23 : List (CPLine V) := e23 :: p22

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d23 : IsCPDerivation formula p23 :=
  IsCPDerivation.div 4 d22 List.mem_cons_self (by decide) (by decide)

def c24 : Clause V := {((0, 1), false), ((1, 1), false)}

def e24 : CPLine V := clauseCP c24

def p24 : List (CPLine V) := e24 :: p23

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d24 : IsCPDerivation formula p24 :=
  IsCPDerivation.ax c24 d23 (Or.inr ⟨0, 1, 1, by decide, rfl⟩)

def c25 : Clause V := {((0, 1), false), ((2, 1), false)}

def e25 : CPLine V := clauseCP c25

def p25 : List (CPLine V) := e25 :: p24

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d25 : IsCPDerivation formula p25 :=
  IsCPDerivation.ax c25 d24 (Or.inr ⟨0, 2, 1, by decide, rfl⟩)

def c26 : Clause V := {((0, 1), false), ((3, 1), false)}

def e26 : CPLine V := clauseCP c26

def p26 : List (CPLine V) := e26 :: p25

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d26 : IsCPDerivation formula p26 :=
  IsCPDerivation.ax c26 d25 (Or.inr ⟨0, 3, 1, by decide, rfl⟩)

def c27 : Clause V := {((0, 1), false), ((4, 1), false)}

def e27 : CPLine V := clauseCP c27

def p27 : List (CPLine V) := e27 :: p26

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d27 : IsCPDerivation formula p27 :=
  IsCPDerivation.ax c27 d26 (Or.inr ⟨0, 4, 1, by decide, rfl⟩)

def c28 : Clause V := {((1, 1), false), ((2, 1), false)}

def e28 : CPLine V := clauseCP c28

def p28 : List (CPLine V) := e28 :: p27

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d28 : IsCPDerivation formula p28 :=
  IsCPDerivation.ax c28 d27 (Or.inr ⟨1, 2, 1, by decide, rfl⟩)

def c29 : Clause V := {((1, 1), false), ((3, 1), false)}

def e29 : CPLine V := clauseCP c29

def p29 : List (CPLine V) := e29 :: p28

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d29 : IsCPDerivation formula p29 :=
  IsCPDerivation.ax c29 d28 (Or.inr ⟨1, 3, 1, by decide, rfl⟩)

def c30 : Clause V := {((1, 1), false), ((4, 1), false)}

def e30 : CPLine V := clauseCP c30

def p30 : List (CPLine V) := e30 :: p29

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d30 : IsCPDerivation formula p30 :=
  IsCPDerivation.ax c30 d29 (Or.inr ⟨1, 4, 1, by decide, rfl⟩)

def c31 : Clause V := {((2, 1), false), ((3, 1), false)}

def e31 : CPLine V := clauseCP c31

def p31 : List (CPLine V) := e31 :: p30

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d31 : IsCPDerivation formula p31 :=
  IsCPDerivation.ax c31 d30 (Or.inr ⟨2, 3, 1, by decide, rfl⟩)

def c32 : Clause V := {((2, 1), false), ((4, 1), false)}

def e32 : CPLine V := clauseCP c32

def p32 : List (CPLine V) := e32 :: p31

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d32 : IsCPDerivation formula p32 :=
  IsCPDerivation.ax c32 d31 (Or.inr ⟨2, 4, 1, by decide, rfl⟩)

def c33 : Clause V := {((3, 1), false), ((4, 1), false)}

def e33 : CPLine V := clauseCP c33

def p33 : List (CPLine V) := e33 :: p32

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d33 : IsCPDerivation formula p33 :=
  IsCPDerivation.ax c33 d32 (Or.inr ⟨3, 4, 1, by decide, rfl⟩)

def e34 : CPLine V := (e25.1 + e28.1, e25.2 + e28.2)

def p34 : List (CPLine V) := e34 :: p33

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d34 : IsCPDerivation formula p34 :=
  IsCPDerivation.add d33 (List.mem_cons_of_mem e33 (List.mem_cons_of_mem e32 (List.mem_cons_of_mem e31 (List.mem_cons_of_mem e30 (List.mem_cons_of_mem e29 (List.mem_cons_of_mem e28 (List.mem_cons_of_mem e27 (List.mem_cons_of_mem e26 List.mem_cons_self)))))))) (List.mem_cons_of_mem e33 (List.mem_cons_of_mem e32 (List.mem_cons_of_mem e31 (List.mem_cons_of_mem e30 (List.mem_cons_of_mem e29 List.mem_cons_self)))))

def e35 : CPLine V := (e24.1 + e34.1, e24.2 + e34.2)

def p35 : List (CPLine V) := e35 :: p34

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d35 : IsCPDerivation formula p35 :=
  IsCPDerivation.add d34 (List.mem_cons_of_mem e34 (List.mem_cons_of_mem e33 (List.mem_cons_of_mem e32 (List.mem_cons_of_mem e31 (List.mem_cons_of_mem e30 (List.mem_cons_of_mem e29 (List.mem_cons_of_mem e28 (List.mem_cons_of_mem e27 (List.mem_cons_of_mem e26 (List.mem_cons_of_mem e25 List.mem_cons_self)))))))))) List.mem_cons_self

def e36 : CPLine V := (fun v => e35.1 v / (2 : ℤ), -((-e35.2) / (2 : ℤ)))

def p36 : List (CPLine V) := e36 :: p35

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d36 : IsCPDerivation formula p36 :=
  IsCPDerivation.div 2 d35 List.mem_cons_self (by decide) (by decide)

def e37 : CPLine V := (e26.1 + e29.1, e26.2 + e29.2)

def p37 : List (CPLine V) := e37 :: p36

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d37 : IsCPDerivation formula p37 :=
  IsCPDerivation.add d36 (List.mem_cons_of_mem e36 (List.mem_cons_of_mem e35 (List.mem_cons_of_mem e34 (List.mem_cons_of_mem e33 (List.mem_cons_of_mem e32 (List.mem_cons_of_mem e31 (List.mem_cons_of_mem e30 (List.mem_cons_of_mem e29 (List.mem_cons_of_mem e28 (List.mem_cons_of_mem e27 List.mem_cons_self)))))))))) (List.mem_cons_of_mem e36 (List.mem_cons_of_mem e35 (List.mem_cons_of_mem e34 (List.mem_cons_of_mem e33 (List.mem_cons_of_mem e32 (List.mem_cons_of_mem e31 (List.mem_cons_of_mem e30 List.mem_cons_self)))))))

def e38 : CPLine V := (e37.1 + e31.1, e37.2 + e31.2)

def p38 : List (CPLine V) := e38 :: p37

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d38 : IsCPDerivation formula p38 :=
  IsCPDerivation.add d37 List.mem_cons_self (List.mem_cons_of_mem e37 (List.mem_cons_of_mem e36 (List.mem_cons_of_mem e35 (List.mem_cons_of_mem e34 (List.mem_cons_of_mem e33 (List.mem_cons_of_mem e32 List.mem_cons_self))))))

def e39 : CPLine V := ((2 : ℤ) • e36.1, (2 : ℤ) * e36.2)

def p39 : List (CPLine V) := e39 :: p38

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d39 : IsCPDerivation formula p39 :=
  IsCPDerivation.mul 2 d38 (List.mem_cons_of_mem e38 (List.mem_cons_of_mem e37 List.mem_cons_self))

def e40 : CPLine V := (e39.1 + e38.1, e39.2 + e38.2)

def p40 : List (CPLine V) := e40 :: p39

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d40 : IsCPDerivation formula p40 :=
  IsCPDerivation.add d39 List.mem_cons_self (List.mem_cons_of_mem e39 List.mem_cons_self)

def e41 : CPLine V := (fun v => e40.1 v / (3 : ℤ), -((-e40.2) / (3 : ℤ)))

def p41 : List (CPLine V) := e41 :: p40

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d41 : IsCPDerivation formula p41 :=
  IsCPDerivation.div 3 d40 List.mem_cons_self (by decide) (by decide)

def e42 : CPLine V := (e27.1 + e30.1, e27.2 + e30.2)

def p42 : List (CPLine V) := e42 :: p41

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d42 : IsCPDerivation formula p42 :=
  IsCPDerivation.add d41 (List.mem_cons_of_mem e41 (List.mem_cons_of_mem e40 (List.mem_cons_of_mem e39 (List.mem_cons_of_mem e38 (List.mem_cons_of_mem e37 (List.mem_cons_of_mem e36 (List.mem_cons_of_mem e35 (List.mem_cons_of_mem e34 (List.mem_cons_of_mem e33 (List.mem_cons_of_mem e32 (List.mem_cons_of_mem e31 (List.mem_cons_of_mem e30 (List.mem_cons_of_mem e29 (List.mem_cons_of_mem e28 List.mem_cons_self)))))))))))))) (List.mem_cons_of_mem e41 (List.mem_cons_of_mem e40 (List.mem_cons_of_mem e39 (List.mem_cons_of_mem e38 (List.mem_cons_of_mem e37 (List.mem_cons_of_mem e36 (List.mem_cons_of_mem e35 (List.mem_cons_of_mem e34 (List.mem_cons_of_mem e33 (List.mem_cons_of_mem e32 (List.mem_cons_of_mem e31 List.mem_cons_self)))))))))))

def e43 : CPLine V := (e42.1 + e32.1, e42.2 + e32.2)

def p43 : List (CPLine V) := e43 :: p42

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d43 : IsCPDerivation formula p43 :=
  IsCPDerivation.add d42 List.mem_cons_self (List.mem_cons_of_mem e42 (List.mem_cons_of_mem e41 (List.mem_cons_of_mem e40 (List.mem_cons_of_mem e39 (List.mem_cons_of_mem e38 (List.mem_cons_of_mem e37 (List.mem_cons_of_mem e36 (List.mem_cons_of_mem e35 (List.mem_cons_of_mem e34 (List.mem_cons_of_mem e33 List.mem_cons_self))))))))))

def e44 : CPLine V := (e43.1 + e33.1, e43.2 + e33.2)

def p44 : List (CPLine V) := e44 :: p43

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d44 : IsCPDerivation formula p44 :=
  IsCPDerivation.add d43 List.mem_cons_self (List.mem_cons_of_mem e43 (List.mem_cons_of_mem e42 (List.mem_cons_of_mem e41 (List.mem_cons_of_mem e40 (List.mem_cons_of_mem e39 (List.mem_cons_of_mem e38 (List.mem_cons_of_mem e37 (List.mem_cons_of_mem e36 (List.mem_cons_of_mem e35 (List.mem_cons_of_mem e34 List.mem_cons_self))))))))))

def e45 : CPLine V := ((3 : ℤ) • e41.1, (3 : ℤ) * e41.2)

def p45 : List (CPLine V) := e45 :: p44

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d45 : IsCPDerivation formula p45 :=
  IsCPDerivation.mul 3 d44 (List.mem_cons_of_mem e44 (List.mem_cons_of_mem e43 (List.mem_cons_of_mem e42 List.mem_cons_self)))

def e46 : CPLine V := (e45.1 + e44.1, e45.2 + e44.2)

def p46 : List (CPLine V) := e46 :: p45

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d46 : IsCPDerivation formula p46 :=
  IsCPDerivation.add d45 List.mem_cons_self (List.mem_cons_of_mem e45 List.mem_cons_self)

def e47 : CPLine V := (fun v => e46.1 v / (4 : ℤ), -((-e46.2) / (4 : ℤ)))

def p47 : List (CPLine V) := e47 :: p46

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d47 : IsCPDerivation formula p47 :=
  IsCPDerivation.div 4 d46 List.mem_cons_self (by decide) (by decide)

def c48 : Clause V := {((0, 2), false), ((1, 2), false)}

def e48 : CPLine V := clauseCP c48

def p48 : List (CPLine V) := e48 :: p47

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d48 : IsCPDerivation formula p48 :=
  IsCPDerivation.ax c48 d47 (Or.inr ⟨0, 1, 2, by decide, rfl⟩)

def c49 : Clause V := {((0, 2), false), ((2, 2), false)}

def e49 : CPLine V := clauseCP c49

def p49 : List (CPLine V) := e49 :: p48

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d49 : IsCPDerivation formula p49 :=
  IsCPDerivation.ax c49 d48 (Or.inr ⟨0, 2, 2, by decide, rfl⟩)

def c50 : Clause V := {((0, 2), false), ((3, 2), false)}

def e50 : CPLine V := clauseCP c50

def p50 : List (CPLine V) := e50 :: p49

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d50 : IsCPDerivation formula p50 :=
  IsCPDerivation.ax c50 d49 (Or.inr ⟨0, 3, 2, by decide, rfl⟩)

def c51 : Clause V := {((0, 2), false), ((4, 2), false)}

def e51 : CPLine V := clauseCP c51

def p51 : List (CPLine V) := e51 :: p50

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d51 : IsCPDerivation formula p51 :=
  IsCPDerivation.ax c51 d50 (Or.inr ⟨0, 4, 2, by decide, rfl⟩)

def c52 : Clause V := {((1, 2), false), ((2, 2), false)}

def e52 : CPLine V := clauseCP c52

def p52 : List (CPLine V) := e52 :: p51

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d52 : IsCPDerivation formula p52 :=
  IsCPDerivation.ax c52 d51 (Or.inr ⟨1, 2, 2, by decide, rfl⟩)

def c53 : Clause V := {((1, 2), false), ((3, 2), false)}

def e53 : CPLine V := clauseCP c53

def p53 : List (CPLine V) := e53 :: p52

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d53 : IsCPDerivation formula p53 :=
  IsCPDerivation.ax c53 d52 (Or.inr ⟨1, 3, 2, by decide, rfl⟩)

def c54 : Clause V := {((1, 2), false), ((4, 2), false)}

def e54 : CPLine V := clauseCP c54

def p54 : List (CPLine V) := e54 :: p53

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d54 : IsCPDerivation formula p54 :=
  IsCPDerivation.ax c54 d53 (Or.inr ⟨1, 4, 2, by decide, rfl⟩)

def c55 : Clause V := {((2, 2), false), ((3, 2), false)}

def e55 : CPLine V := clauseCP c55

def p55 : List (CPLine V) := e55 :: p54

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d55 : IsCPDerivation formula p55 :=
  IsCPDerivation.ax c55 d54 (Or.inr ⟨2, 3, 2, by decide, rfl⟩)

def c56 : Clause V := {((2, 2), false), ((4, 2), false)}

def e56 : CPLine V := clauseCP c56

def p56 : List (CPLine V) := e56 :: p55

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d56 : IsCPDerivation formula p56 :=
  IsCPDerivation.ax c56 d55 (Or.inr ⟨2, 4, 2, by decide, rfl⟩)

def c57 : Clause V := {((3, 2), false), ((4, 2), false)}

def e57 : CPLine V := clauseCP c57

def p57 : List (CPLine V) := e57 :: p56

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d57 : IsCPDerivation formula p57 :=
  IsCPDerivation.ax c57 d56 (Or.inr ⟨3, 4, 2, by decide, rfl⟩)

def e58 : CPLine V := (e49.1 + e52.1, e49.2 + e52.2)

def p58 : List (CPLine V) := e58 :: p57

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d58 : IsCPDerivation formula p58 :=
  IsCPDerivation.add d57 (List.mem_cons_of_mem e57 (List.mem_cons_of_mem e56 (List.mem_cons_of_mem e55 (List.mem_cons_of_mem e54 (List.mem_cons_of_mem e53 (List.mem_cons_of_mem e52 (List.mem_cons_of_mem e51 (List.mem_cons_of_mem e50 List.mem_cons_self)))))))) (List.mem_cons_of_mem e57 (List.mem_cons_of_mem e56 (List.mem_cons_of_mem e55 (List.mem_cons_of_mem e54 (List.mem_cons_of_mem e53 List.mem_cons_self)))))

def e59 : CPLine V := (e48.1 + e58.1, e48.2 + e58.2)

def p59 : List (CPLine V) := e59 :: p58

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d59 : IsCPDerivation formula p59 :=
  IsCPDerivation.add d58 (List.mem_cons_of_mem e58 (List.mem_cons_of_mem e57 (List.mem_cons_of_mem e56 (List.mem_cons_of_mem e55 (List.mem_cons_of_mem e54 (List.mem_cons_of_mem e53 (List.mem_cons_of_mem e52 (List.mem_cons_of_mem e51 (List.mem_cons_of_mem e50 (List.mem_cons_of_mem e49 List.mem_cons_self)))))))))) List.mem_cons_self

def e60 : CPLine V := (fun v => e59.1 v / (2 : ℤ), -((-e59.2) / (2 : ℤ)))

def p60 : List (CPLine V) := e60 :: p59

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d60 : IsCPDerivation formula p60 :=
  IsCPDerivation.div 2 d59 List.mem_cons_self (by decide) (by decide)

def e61 : CPLine V := (e50.1 + e53.1, e50.2 + e53.2)

def p61 : List (CPLine V) := e61 :: p60

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d61 : IsCPDerivation formula p61 :=
  IsCPDerivation.add d60 (List.mem_cons_of_mem e60 (List.mem_cons_of_mem e59 (List.mem_cons_of_mem e58 (List.mem_cons_of_mem e57 (List.mem_cons_of_mem e56 (List.mem_cons_of_mem e55 (List.mem_cons_of_mem e54 (List.mem_cons_of_mem e53 (List.mem_cons_of_mem e52 (List.mem_cons_of_mem e51 List.mem_cons_self)))))))))) (List.mem_cons_of_mem e60 (List.mem_cons_of_mem e59 (List.mem_cons_of_mem e58 (List.mem_cons_of_mem e57 (List.mem_cons_of_mem e56 (List.mem_cons_of_mem e55 (List.mem_cons_of_mem e54 List.mem_cons_self)))))))

def e62 : CPLine V := (e61.1 + e55.1, e61.2 + e55.2)

def p62 : List (CPLine V) := e62 :: p61

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d62 : IsCPDerivation formula p62 :=
  IsCPDerivation.add d61 List.mem_cons_self (List.mem_cons_of_mem e61 (List.mem_cons_of_mem e60 (List.mem_cons_of_mem e59 (List.mem_cons_of_mem e58 (List.mem_cons_of_mem e57 (List.mem_cons_of_mem e56 List.mem_cons_self))))))

def e63 : CPLine V := ((2 : ℤ) • e60.1, (2 : ℤ) * e60.2)

def p63 : List (CPLine V) := e63 :: p62

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d63 : IsCPDerivation formula p63 :=
  IsCPDerivation.mul 2 d62 (List.mem_cons_of_mem e62 (List.mem_cons_of_mem e61 List.mem_cons_self))

def e64 : CPLine V := (e63.1 + e62.1, e63.2 + e62.2)

def p64 : List (CPLine V) := e64 :: p63

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d64 : IsCPDerivation formula p64 :=
  IsCPDerivation.add d63 List.mem_cons_self (List.mem_cons_of_mem e63 List.mem_cons_self)

def e65 : CPLine V := (fun v => e64.1 v / (3 : ℤ), -((-e64.2) / (3 : ℤ)))

def p65 : List (CPLine V) := e65 :: p64

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d65 : IsCPDerivation formula p65 :=
  IsCPDerivation.div 3 d64 List.mem_cons_self (by decide) (by decide)

def e66 : CPLine V := (e51.1 + e54.1, e51.2 + e54.2)

def p66 : List (CPLine V) := e66 :: p65

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d66 : IsCPDerivation formula p66 :=
  IsCPDerivation.add d65 (List.mem_cons_of_mem e65 (List.mem_cons_of_mem e64 (List.mem_cons_of_mem e63 (List.mem_cons_of_mem e62 (List.mem_cons_of_mem e61 (List.mem_cons_of_mem e60 (List.mem_cons_of_mem e59 (List.mem_cons_of_mem e58 (List.mem_cons_of_mem e57 (List.mem_cons_of_mem e56 (List.mem_cons_of_mem e55 (List.mem_cons_of_mem e54 (List.mem_cons_of_mem e53 (List.mem_cons_of_mem e52 List.mem_cons_self)))))))))))))) (List.mem_cons_of_mem e65 (List.mem_cons_of_mem e64 (List.mem_cons_of_mem e63 (List.mem_cons_of_mem e62 (List.mem_cons_of_mem e61 (List.mem_cons_of_mem e60 (List.mem_cons_of_mem e59 (List.mem_cons_of_mem e58 (List.mem_cons_of_mem e57 (List.mem_cons_of_mem e56 (List.mem_cons_of_mem e55 List.mem_cons_self)))))))))))

def e67 : CPLine V := (e66.1 + e56.1, e66.2 + e56.2)

def p67 : List (CPLine V) := e67 :: p66

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d67 : IsCPDerivation formula p67 :=
  IsCPDerivation.add d66 List.mem_cons_self (List.mem_cons_of_mem e66 (List.mem_cons_of_mem e65 (List.mem_cons_of_mem e64 (List.mem_cons_of_mem e63 (List.mem_cons_of_mem e62 (List.mem_cons_of_mem e61 (List.mem_cons_of_mem e60 (List.mem_cons_of_mem e59 (List.mem_cons_of_mem e58 (List.mem_cons_of_mem e57 List.mem_cons_self))))))))))

def e68 : CPLine V := (e67.1 + e57.1, e67.2 + e57.2)

def p68 : List (CPLine V) := e68 :: p67

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d68 : IsCPDerivation formula p68 :=
  IsCPDerivation.add d67 List.mem_cons_self (List.mem_cons_of_mem e67 (List.mem_cons_of_mem e66 (List.mem_cons_of_mem e65 (List.mem_cons_of_mem e64 (List.mem_cons_of_mem e63 (List.mem_cons_of_mem e62 (List.mem_cons_of_mem e61 (List.mem_cons_of_mem e60 (List.mem_cons_of_mem e59 (List.mem_cons_of_mem e58 List.mem_cons_self))))))))))

def e69 : CPLine V := ((3 : ℤ) • e65.1, (3 : ℤ) * e65.2)

def p69 : List (CPLine V) := e69 :: p68

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d69 : IsCPDerivation formula p69 :=
  IsCPDerivation.mul 3 d68 (List.mem_cons_of_mem e68 (List.mem_cons_of_mem e67 (List.mem_cons_of_mem e66 List.mem_cons_self)))

def e70 : CPLine V := (e69.1 + e68.1, e69.2 + e68.2)

def p70 : List (CPLine V) := e70 :: p69

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d70 : IsCPDerivation formula p70 :=
  IsCPDerivation.add d69 List.mem_cons_self (List.mem_cons_of_mem e69 List.mem_cons_self)

def e71 : CPLine V := (fun v => e70.1 v / (4 : ℤ), -((-e70.2) / (4 : ℤ)))

def p71 : List (CPLine V) := e71 :: p70

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d71 : IsCPDerivation formula p71 :=
  IsCPDerivation.div 4 d70 List.mem_cons_self (by decide) (by decide)

def c72 : Clause V := {((0, 3), false), ((1, 3), false)}

def e72 : CPLine V := clauseCP c72

def p72 : List (CPLine V) := e72 :: p71

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d72 : IsCPDerivation formula p72 :=
  IsCPDerivation.ax c72 d71 (Or.inr ⟨0, 1, 3, by decide, rfl⟩)

def c73 : Clause V := {((0, 3), false), ((2, 3), false)}

def e73 : CPLine V := clauseCP c73

def p73 : List (CPLine V) := e73 :: p72

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d73 : IsCPDerivation formula p73 :=
  IsCPDerivation.ax c73 d72 (Or.inr ⟨0, 2, 3, by decide, rfl⟩)

def c74 : Clause V := {((0, 3), false), ((3, 3), false)}

def e74 : CPLine V := clauseCP c74

def p74 : List (CPLine V) := e74 :: p73

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d74 : IsCPDerivation formula p74 :=
  IsCPDerivation.ax c74 d73 (Or.inr ⟨0, 3, 3, by decide, rfl⟩)

def c75 : Clause V := {((0, 3), false), ((4, 3), false)}

def e75 : CPLine V := clauseCP c75

def p75 : List (CPLine V) := e75 :: p74

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d75 : IsCPDerivation formula p75 :=
  IsCPDerivation.ax c75 d74 (Or.inr ⟨0, 4, 3, by decide, rfl⟩)

def c76 : Clause V := {((1, 3), false), ((2, 3), false)}

def e76 : CPLine V := clauseCP c76

def p76 : List (CPLine V) := e76 :: p75

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d76 : IsCPDerivation formula p76 :=
  IsCPDerivation.ax c76 d75 (Or.inr ⟨1, 2, 3, by decide, rfl⟩)

def c77 : Clause V := {((1, 3), false), ((3, 3), false)}

def e77 : CPLine V := clauseCP c77

def p77 : List (CPLine V) := e77 :: p76

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d77 : IsCPDerivation formula p77 :=
  IsCPDerivation.ax c77 d76 (Or.inr ⟨1, 3, 3, by decide, rfl⟩)

def c78 : Clause V := {((1, 3), false), ((4, 3), false)}

def e78 : CPLine V := clauseCP c78

def p78 : List (CPLine V) := e78 :: p77

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d78 : IsCPDerivation formula p78 :=
  IsCPDerivation.ax c78 d77 (Or.inr ⟨1, 4, 3, by decide, rfl⟩)

def c79 : Clause V := {((2, 3), false), ((3, 3), false)}

def e79 : CPLine V := clauseCP c79

def p79 : List (CPLine V) := e79 :: p78

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d79 : IsCPDerivation formula p79 :=
  IsCPDerivation.ax c79 d78 (Or.inr ⟨2, 3, 3, by decide, rfl⟩)

def c80 : Clause V := {((2, 3), false), ((4, 3), false)}

def e80 : CPLine V := clauseCP c80

def p80 : List (CPLine V) := e80 :: p79

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d80 : IsCPDerivation formula p80 :=
  IsCPDerivation.ax c80 d79 (Or.inr ⟨2, 4, 3, by decide, rfl⟩)

def c81 : Clause V := {((3, 3), false), ((4, 3), false)}

def e81 : CPLine V := clauseCP c81

def p81 : List (CPLine V) := e81 :: p80

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d81 : IsCPDerivation formula p81 :=
  IsCPDerivation.ax c81 d80 (Or.inr ⟨3, 4, 3, by decide, rfl⟩)

def e82 : CPLine V := (e73.1 + e76.1, e73.2 + e76.2)

def p82 : List (CPLine V) := e82 :: p81

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d82 : IsCPDerivation formula p82 :=
  IsCPDerivation.add d81 (List.mem_cons_of_mem e81 (List.mem_cons_of_mem e80 (List.mem_cons_of_mem e79 (List.mem_cons_of_mem e78 (List.mem_cons_of_mem e77 (List.mem_cons_of_mem e76 (List.mem_cons_of_mem e75 (List.mem_cons_of_mem e74 List.mem_cons_self)))))))) (List.mem_cons_of_mem e81 (List.mem_cons_of_mem e80 (List.mem_cons_of_mem e79 (List.mem_cons_of_mem e78 (List.mem_cons_of_mem e77 List.mem_cons_self)))))

def e83 : CPLine V := (e72.1 + e82.1, e72.2 + e82.2)

def p83 : List (CPLine V) := e83 :: p82

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d83 : IsCPDerivation formula p83 :=
  IsCPDerivation.add d82 (List.mem_cons_of_mem e82 (List.mem_cons_of_mem e81 (List.mem_cons_of_mem e80 (List.mem_cons_of_mem e79 (List.mem_cons_of_mem e78 (List.mem_cons_of_mem e77 (List.mem_cons_of_mem e76 (List.mem_cons_of_mem e75 (List.mem_cons_of_mem e74 (List.mem_cons_of_mem e73 List.mem_cons_self)))))))))) List.mem_cons_self

def e84 : CPLine V := (fun v => e83.1 v / (2 : ℤ), -((-e83.2) / (2 : ℤ)))

def p84 : List (CPLine V) := e84 :: p83

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d84 : IsCPDerivation formula p84 :=
  IsCPDerivation.div 2 d83 List.mem_cons_self (by decide) (by decide)

def e85 : CPLine V := (e74.1 + e77.1, e74.2 + e77.2)

def p85 : List (CPLine V) := e85 :: p84

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d85 : IsCPDerivation formula p85 :=
  IsCPDerivation.add d84 (List.mem_cons_of_mem e84 (List.mem_cons_of_mem e83 (List.mem_cons_of_mem e82 (List.mem_cons_of_mem e81 (List.mem_cons_of_mem e80 (List.mem_cons_of_mem e79 (List.mem_cons_of_mem e78 (List.mem_cons_of_mem e77 (List.mem_cons_of_mem e76 (List.mem_cons_of_mem e75 List.mem_cons_self)))))))))) (List.mem_cons_of_mem e84 (List.mem_cons_of_mem e83 (List.mem_cons_of_mem e82 (List.mem_cons_of_mem e81 (List.mem_cons_of_mem e80 (List.mem_cons_of_mem e79 (List.mem_cons_of_mem e78 List.mem_cons_self)))))))

def e86 : CPLine V := (e85.1 + e79.1, e85.2 + e79.2)

def p86 : List (CPLine V) := e86 :: p85

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d86 : IsCPDerivation formula p86 :=
  IsCPDerivation.add d85 List.mem_cons_self (List.mem_cons_of_mem e85 (List.mem_cons_of_mem e84 (List.mem_cons_of_mem e83 (List.mem_cons_of_mem e82 (List.mem_cons_of_mem e81 (List.mem_cons_of_mem e80 List.mem_cons_self))))))

def e87 : CPLine V := ((2 : ℤ) • e84.1, (2 : ℤ) * e84.2)

def p87 : List (CPLine V) := e87 :: p86

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d87 : IsCPDerivation formula p87 :=
  IsCPDerivation.mul 2 d86 (List.mem_cons_of_mem e86 (List.mem_cons_of_mem e85 List.mem_cons_self))

def e88 : CPLine V := (e87.1 + e86.1, e87.2 + e86.2)

def p88 : List (CPLine V) := e88 :: p87

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d88 : IsCPDerivation formula p88 :=
  IsCPDerivation.add d87 List.mem_cons_self (List.mem_cons_of_mem e87 List.mem_cons_self)

def e89 : CPLine V := (fun v => e88.1 v / (3 : ℤ), -((-e88.2) / (3 : ℤ)))

def p89 : List (CPLine V) := e89 :: p88

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d89 : IsCPDerivation formula p89 :=
  IsCPDerivation.div 3 d88 List.mem_cons_self (by decide) (by decide)

def e90 : CPLine V := (e75.1 + e78.1, e75.2 + e78.2)

def p90 : List (CPLine V) := e90 :: p89

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d90 : IsCPDerivation formula p90 :=
  IsCPDerivation.add d89 (List.mem_cons_of_mem e89 (List.mem_cons_of_mem e88 (List.mem_cons_of_mem e87 (List.mem_cons_of_mem e86 (List.mem_cons_of_mem e85 (List.mem_cons_of_mem e84 (List.mem_cons_of_mem e83 (List.mem_cons_of_mem e82 (List.mem_cons_of_mem e81 (List.mem_cons_of_mem e80 (List.mem_cons_of_mem e79 (List.mem_cons_of_mem e78 (List.mem_cons_of_mem e77 (List.mem_cons_of_mem e76 List.mem_cons_self)))))))))))))) (List.mem_cons_of_mem e89 (List.mem_cons_of_mem e88 (List.mem_cons_of_mem e87 (List.mem_cons_of_mem e86 (List.mem_cons_of_mem e85 (List.mem_cons_of_mem e84 (List.mem_cons_of_mem e83 (List.mem_cons_of_mem e82 (List.mem_cons_of_mem e81 (List.mem_cons_of_mem e80 (List.mem_cons_of_mem e79 List.mem_cons_self)))))))))))

def e91 : CPLine V := (e90.1 + e80.1, e90.2 + e80.2)

def p91 : List (CPLine V) := e91 :: p90

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d91 : IsCPDerivation formula p91 :=
  IsCPDerivation.add d90 List.mem_cons_self (List.mem_cons_of_mem e90 (List.mem_cons_of_mem e89 (List.mem_cons_of_mem e88 (List.mem_cons_of_mem e87 (List.mem_cons_of_mem e86 (List.mem_cons_of_mem e85 (List.mem_cons_of_mem e84 (List.mem_cons_of_mem e83 (List.mem_cons_of_mem e82 (List.mem_cons_of_mem e81 List.mem_cons_self))))))))))

def e92 : CPLine V := (e91.1 + e81.1, e91.2 + e81.2)

def p92 : List (CPLine V) := e92 :: p91

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d92 : IsCPDerivation formula p92 :=
  IsCPDerivation.add d91 List.mem_cons_self (List.mem_cons_of_mem e91 (List.mem_cons_of_mem e90 (List.mem_cons_of_mem e89 (List.mem_cons_of_mem e88 (List.mem_cons_of_mem e87 (List.mem_cons_of_mem e86 (List.mem_cons_of_mem e85 (List.mem_cons_of_mem e84 (List.mem_cons_of_mem e83 (List.mem_cons_of_mem e82 List.mem_cons_self))))))))))

def e93 : CPLine V := ((3 : ℤ) • e89.1, (3 : ℤ) * e89.2)

def p93 : List (CPLine V) := e93 :: p92

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d93 : IsCPDerivation formula p93 :=
  IsCPDerivation.mul 3 d92 (List.mem_cons_of_mem e92 (List.mem_cons_of_mem e91 (List.mem_cons_of_mem e90 List.mem_cons_self)))

def e94 : CPLine V := (e93.1 + e92.1, e93.2 + e92.2)

def p94 : List (CPLine V) := e94 :: p93

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d94 : IsCPDerivation formula p94 :=
  IsCPDerivation.add d93 List.mem_cons_self (List.mem_cons_of_mem e93 List.mem_cons_self)

def e95 : CPLine V := (fun v => e94.1 v / (4 : ℤ), -((-e94.2) / (4 : ℤ)))

def p95 : List (CPLine V) := e95 :: p94

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d95 : IsCPDerivation formula p95 :=
  IsCPDerivation.div 4 d94 List.mem_cons_self (by decide) (by decide)

def c96 : Clause V := Finset.univ.image (fun h : Fin 4 => (((0 : Fin 5), h), true))

def e96 : CPLine V := clauseCP c96

def p96 : List (CPLine V) := e96 :: p95

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d96 : IsCPDerivation formula p96 :=
  IsCPDerivation.ax c96 d95 (Or.inl ⟨0, rfl⟩)

def c97 : Clause V := Finset.univ.image (fun h : Fin 4 => (((1 : Fin 5), h), true))

def e97 : CPLine V := clauseCP c97

def p97 : List (CPLine V) := e97 :: p96

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d97 : IsCPDerivation formula p97 :=
  IsCPDerivation.ax c97 d96 (Or.inl ⟨1, rfl⟩)

def e98 : CPLine V := (e96.1 + e97.1, e96.2 + e97.2)

def p98 : List (CPLine V) := e98 :: p97

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d98 : IsCPDerivation formula p98 :=
  IsCPDerivation.add d97 (List.mem_cons_of_mem e97 List.mem_cons_self) List.mem_cons_self

def c99 : Clause V := Finset.univ.image (fun h : Fin 4 => (((2 : Fin 5), h), true))

def e99 : CPLine V := clauseCP c99

def p99 : List (CPLine V) := e99 :: p98

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d99 : IsCPDerivation formula p99 :=
  IsCPDerivation.ax c99 d98 (Or.inl ⟨2, rfl⟩)

def e100 : CPLine V := (e98.1 + e99.1, e98.2 + e99.2)

def p100 : List (CPLine V) := e100 :: p99

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d100 : IsCPDerivation formula p100 :=
  IsCPDerivation.add d99 (List.mem_cons_of_mem e99 List.mem_cons_self) List.mem_cons_self

def c101 : Clause V := Finset.univ.image (fun h : Fin 4 => (((3 : Fin 5), h), true))

def e101 : CPLine V := clauseCP c101

def p101 : List (CPLine V) := e101 :: p100

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d101 : IsCPDerivation formula p101 :=
  IsCPDerivation.ax c101 d100 (Or.inl ⟨3, rfl⟩)

def e102 : CPLine V := (e100.1 + e101.1, e100.2 + e101.2)

def p102 : List (CPLine V) := e102 :: p101

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d102 : IsCPDerivation formula p102 :=
  IsCPDerivation.add d101 (List.mem_cons_of_mem e101 List.mem_cons_self) List.mem_cons_self

def c103 : Clause V := Finset.univ.image (fun h : Fin 4 => (((4 : Fin 5), h), true))

def e103 : CPLine V := clauseCP c103

def p103 : List (CPLine V) := e103 :: p102

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d103 : IsCPDerivation formula p103 :=
  IsCPDerivation.ax c103 d102 (Or.inl ⟨4, rfl⟩)

def e104 : CPLine V := (e102.1 + e103.1, e102.2 + e103.2)

def p104 : List (CPLine V) := e104 :: p103

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d104 : IsCPDerivation formula p104 :=
  IsCPDerivation.add d103 (List.mem_cons_of_mem e103 List.mem_cons_self) List.mem_cons_self

def e105 : CPLine V := (e23.1 + e47.1, e23.2 + e47.2)

def p105 : List (CPLine V) := e105 :: p104

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d105 : IsCPDerivation formula p105 :=
  IsCPDerivation.add d104 (List.mem_cons_of_mem e104 (List.mem_cons_of_mem e103 (List.mem_cons_of_mem e102 (List.mem_cons_of_mem e101 (List.mem_cons_of_mem e100 (List.mem_cons_of_mem e99 (List.mem_cons_of_mem e98 (List.mem_cons_of_mem e97 (List.mem_cons_of_mem e96 (List.mem_cons_of_mem e95 (List.mem_cons_of_mem e94 (List.mem_cons_of_mem e93 (List.mem_cons_of_mem e92 (List.mem_cons_of_mem e91 (List.mem_cons_of_mem e90 (List.mem_cons_of_mem e89 (List.mem_cons_of_mem e88 (List.mem_cons_of_mem e87 (List.mem_cons_of_mem e86 (List.mem_cons_of_mem e85 (List.mem_cons_of_mem e84 (List.mem_cons_of_mem e83 (List.mem_cons_of_mem e82 (List.mem_cons_of_mem e81 (List.mem_cons_of_mem e80 (List.mem_cons_of_mem e79 (List.mem_cons_of_mem e78 (List.mem_cons_of_mem e77 (List.mem_cons_of_mem e76 (List.mem_cons_of_mem e75 (List.mem_cons_of_mem e74 (List.mem_cons_of_mem e73 (List.mem_cons_of_mem e72 (List.mem_cons_of_mem e71 (List.mem_cons_of_mem e70 (List.mem_cons_of_mem e69 (List.mem_cons_of_mem e68 (List.mem_cons_of_mem e67 (List.mem_cons_of_mem e66 (List.mem_cons_of_mem e65 (List.mem_cons_of_mem e64 (List.mem_cons_of_mem e63 (List.mem_cons_of_mem e62 (List.mem_cons_of_mem e61 (List.mem_cons_of_mem e60 (List.mem_cons_of_mem e59 (List.mem_cons_of_mem e58 (List.mem_cons_of_mem e57 (List.mem_cons_of_mem e56 (List.mem_cons_of_mem e55 (List.mem_cons_of_mem e54 (List.mem_cons_of_mem e53 (List.mem_cons_of_mem e52 (List.mem_cons_of_mem e51 (List.mem_cons_of_mem e50 (List.mem_cons_of_mem e49 (List.mem_cons_of_mem e48 (List.mem_cons_of_mem e47 (List.mem_cons_of_mem e46 (List.mem_cons_of_mem e45 (List.mem_cons_of_mem e44 (List.mem_cons_of_mem e43 (List.mem_cons_of_mem e42 (List.mem_cons_of_mem e41 (List.mem_cons_of_mem e40 (List.mem_cons_of_mem e39 (List.mem_cons_of_mem e38 (List.mem_cons_of_mem e37 (List.mem_cons_of_mem e36 (List.mem_cons_of_mem e35 (List.mem_cons_of_mem e34 (List.mem_cons_of_mem e33 (List.mem_cons_of_mem e32 (List.mem_cons_of_mem e31 (List.mem_cons_of_mem e30 (List.mem_cons_of_mem e29 (List.mem_cons_of_mem e28 (List.mem_cons_of_mem e27 (List.mem_cons_of_mem e26 (List.mem_cons_of_mem e25 (List.mem_cons_of_mem e24 List.mem_cons_self))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (List.mem_cons_of_mem e104 (List.mem_cons_of_mem e103 (List.mem_cons_of_mem e102 (List.mem_cons_of_mem e101 (List.mem_cons_of_mem e100 (List.mem_cons_of_mem e99 (List.mem_cons_of_mem e98 (List.mem_cons_of_mem e97 (List.mem_cons_of_mem e96 (List.mem_cons_of_mem e95 (List.mem_cons_of_mem e94 (List.mem_cons_of_mem e93 (List.mem_cons_of_mem e92 (List.mem_cons_of_mem e91 (List.mem_cons_of_mem e90 (List.mem_cons_of_mem e89 (List.mem_cons_of_mem e88 (List.mem_cons_of_mem e87 (List.mem_cons_of_mem e86 (List.mem_cons_of_mem e85 (List.mem_cons_of_mem e84 (List.mem_cons_of_mem e83 (List.mem_cons_of_mem e82 (List.mem_cons_of_mem e81 (List.mem_cons_of_mem e80 (List.mem_cons_of_mem e79 (List.mem_cons_of_mem e78 (List.mem_cons_of_mem e77 (List.mem_cons_of_mem e76 (List.mem_cons_of_mem e75 (List.mem_cons_of_mem e74 (List.mem_cons_of_mem e73 (List.mem_cons_of_mem e72 (List.mem_cons_of_mem e71 (List.mem_cons_of_mem e70 (List.mem_cons_of_mem e69 (List.mem_cons_of_mem e68 (List.mem_cons_of_mem e67 (List.mem_cons_of_mem e66 (List.mem_cons_of_mem e65 (List.mem_cons_of_mem e64 (List.mem_cons_of_mem e63 (List.mem_cons_of_mem e62 (List.mem_cons_of_mem e61 (List.mem_cons_of_mem e60 (List.mem_cons_of_mem e59 (List.mem_cons_of_mem e58 (List.mem_cons_of_mem e57 (List.mem_cons_of_mem e56 (List.mem_cons_of_mem e55 (List.mem_cons_of_mem e54 (List.mem_cons_of_mem e53 (List.mem_cons_of_mem e52 (List.mem_cons_of_mem e51 (List.mem_cons_of_mem e50 (List.mem_cons_of_mem e49 (List.mem_cons_of_mem e48 List.mem_cons_self)))))))))))))))))))))))))))))))))))))))))))))))))))))))))

def e106 : CPLine V := (e105.1 + e71.1, e105.2 + e71.2)

def p106 : List (CPLine V) := e106 :: p105

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d106 : IsCPDerivation formula p106 :=
  IsCPDerivation.add d105 List.mem_cons_self (List.mem_cons_of_mem e105 (List.mem_cons_of_mem e104 (List.mem_cons_of_mem e103 (List.mem_cons_of_mem e102 (List.mem_cons_of_mem e101 (List.mem_cons_of_mem e100 (List.mem_cons_of_mem e99 (List.mem_cons_of_mem e98 (List.mem_cons_of_mem e97 (List.mem_cons_of_mem e96 (List.mem_cons_of_mem e95 (List.mem_cons_of_mem e94 (List.mem_cons_of_mem e93 (List.mem_cons_of_mem e92 (List.mem_cons_of_mem e91 (List.mem_cons_of_mem e90 (List.mem_cons_of_mem e89 (List.mem_cons_of_mem e88 (List.mem_cons_of_mem e87 (List.mem_cons_of_mem e86 (List.mem_cons_of_mem e85 (List.mem_cons_of_mem e84 (List.mem_cons_of_mem e83 (List.mem_cons_of_mem e82 (List.mem_cons_of_mem e81 (List.mem_cons_of_mem e80 (List.mem_cons_of_mem e79 (List.mem_cons_of_mem e78 (List.mem_cons_of_mem e77 (List.mem_cons_of_mem e76 (List.mem_cons_of_mem e75 (List.mem_cons_of_mem e74 (List.mem_cons_of_mem e73 (List.mem_cons_of_mem e72 List.mem_cons_self))))))))))))))))))))))))))))))))))

def e107 : CPLine V := (e106.1 + e95.1, e106.2 + e95.2)

def p107 : List (CPLine V) := e107 :: p106

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d107 : IsCPDerivation formula p107 :=
  IsCPDerivation.add d106 List.mem_cons_self (List.mem_cons_of_mem e106 (List.mem_cons_of_mem e105 (List.mem_cons_of_mem e104 (List.mem_cons_of_mem e103 (List.mem_cons_of_mem e102 (List.mem_cons_of_mem e101 (List.mem_cons_of_mem e100 (List.mem_cons_of_mem e99 (List.mem_cons_of_mem e98 (List.mem_cons_of_mem e97 (List.mem_cons_of_mem e96 List.mem_cons_self)))))))))))

def e108 : CPLine V := (e104.1 + e107.1, e104.2 + e107.2)

def p108 : List (CPLine V) := e108 :: p107

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem d108 : IsCPDerivation formula p108 :=
  IsCPDerivation.add d107 (List.mem_cons_of_mem e107 (List.mem_cons_of_mem e106 (List.mem_cons_of_mem e105 List.mem_cons_self))) List.mem_cons_self

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem final_line : e108 = ((0 : V → ℤ), (1 : ℤ)) := by
  apply Prod.ext
  · funext v
    have h : ∀ u : V, e108.1 u = 0 := by decide
    exact h v
  · decide

/- A kernel-checked baseline, one line above the assigned cutoff. -/
set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem baseline109 : ∃ π : List (CPLine V), IsCPRefutation formula π ∧ π.length ≤ 109 := by
  refine ⟨p108, ⟨d108, ?_⟩, by decide⟩
  rw [← final_line]
  exact List.mem_cons_self

open scoped BigOperators

/- Each of these 45 assignments falsifies exactly one PHP clause. -/
def critical (i : Fin 45) (v : V) : Bool :=
  Nat.testBit (([541200, 541185, 540705, 525345, 33825, 541201, 540961, 529441, 99361, 540946, 529426, 99346, 528706, 98626, 71746, 540962, 541202, 533522, 164882, 541217, 533537, 164897, 533057, 164417, 141377, 532804, 533524, 541204, 295444, 533569, 541249, 295489, 541729, 295969, 280609, 270728, 272408, 295448, 541208, 272513, 295553, 541313, 296993, 542753, 558113] : List ℕ).getD i.val 0) (v.1.val * 4 + v.2.val)

def bad (e : CPLine V) : Finset (Fin 45) :=
  Finset.univ.filter (fun i => (∑ v : V, e.1 v * (if critical i v then 1 else 0)) < e.2)

@[simp] theorem mem_bad (i : Fin 45) (e : CPLine V) :
    i ∈ bad e ↔ ¬ CPLine.Holds (critical i) e := by
  simp [bad, CPLine.Holds, not_le]

def pigeonClause (p : Fin 5) : Clause V :=
  Finset.univ.image (fun h : Fin 4 => ((p, h), true))

def pairClause (p q : Fin 5) (h : Fin 4) : Clause V :=
  {((p, h), false), ((q, h), false)}

def pigeonLine (p : Fin 5) : CPLine V :=
  (fun v => if v.1 = p then 1 else 0, 1)

def pairLine (p q : Fin 5) (h : Fin 4) : CPLine V :=
  (fun v => if v = (p, h) ∨ v = (q, h) then -1 else 0, -1)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 20000000 in
theorem pigeon_values : ∀ p : Fin 5,
    (∀ v : V, (clauseCP (pigeonClause p)).1 v = (pigeonLine p).1 v) ∧
    (clauseCP (pigeonClause p)).2 = (pigeonLine p).2 := by
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 20000000 in
theorem pair_values : ∀ p q : Fin 5, ∀ h : Fin 4, p ≠ q →
    (∀ v : V, (clauseCP (pairClause p q h)).1 v = (pairLine p q h).1 v) ∧
    (clauseCP (pairClause p q h)).2 = (pairLine p q h).2 := by
  decide

theorem pigeon_line_eq (p : Fin 5) : clauseCP (pigeonClause p) = pigeonLine p :=
  Prod.ext (funext (pigeon_values p).1) (pigeon_values p).2

theorem pair_line_eq (p q : Fin 5) (h : Fin 4) (hne : p ≠ q) :
    clauseCP (pairClause p q h) = pairLine p q h :=
  Prod.ext (funext (pair_values p q h hne).1) (pair_values p q h hne).2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 20000000 in
theorem pigeon_bad_bound : ∀ p : Fin 5, (bad (pigeonLine p)).card ≤ 1 := by
  decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 20000000 in
theorem pair_bad_bound : ∀ p q : Fin 5, ∀ h : Fin 4, p ≠ q →
    (bad (pairLine p q h)).card ≤ 1 := by
  decide

theorem axiom_bad_bound (C : Clause V) (hC : C ∈ formula) :
    (bad (clauseCP C)).card ≤ 1 := by
  rcases hC with ⟨p, rfl⟩ | ⟨p, q, h, hne, rfl⟩
  · change (bad (clauseCP (pigeonClause p))).card ≤ 1
    rw [pigeon_line_eq]
    exact pigeon_bad_bound p
  · change (bad (clauseCP (pairClause p q h))).card ≤ 1
    rw [pair_line_eq p q h hne]
    exact pair_bad_bound p q h hne

theorem bad_contradiction : bad ((0 : V → ℤ), 1) = Finset.univ := by
  ext i
  simp [bad]

theorem holds_boolLo (a : V → Bool) (v : V) :
    CPLine.Holds a ((fun u => if u = v then 1 else 0, 0) : CPLine V) := by
  unfold CPLine.Holds
  exact Finset.sum_nonneg fun u _ => by dsimp only; split_ifs <;> norm_num

/-- The Boolean input constraint `-x_v ≥ -1` holds everywhere. -/
theorem holds_boolHi (a : V → Bool) (v : V) :
    CPLine.Holds a ((fun u => if u = v then -1 else 0, -1) : CPLine V) := by
  have hs : (∑ u, (if u = v then (-1 : ℤ) else 0) * (if a u then 1 else 0))
      = (-1) * (if a v then 1 else 0) := by
    rw [Finset.sum_eq_single v]
    · simp
    · intro u _ hu
      simp [hu]
    · intro h
      exact absurd (Finset.mem_univ v) h
  unfold CPLine.Holds
  dsimp only
  rw [hs]
  split_ifs <;> norm_num

/-- Addition is sound pointwise. -/
theorem holds_add {a : V → Bool} {e e' : CPLine V}
    (h : CPLine.Holds a e) (h' : CPLine.Holds a e') :
    CPLine.Holds a ((e.1 + e'.1, e.2 + e'.2) : CPLine V) := by
  unfold CPLine.Holds at *
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  linarith

/-- Multiplication by a natural number (possibly zero) is sound pointwise. -/
theorem holds_mul {a : V → Bool} {e : CPLine V} (k : ℕ)
    (h : CPLine.Holds a e) :
    CPLine.Holds a (((k : ℤ) • e.1, (k : ℤ) * e.2) : CPLine V) := by
  unfold CPLine.Holds at *
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left h (Int.natCast_nonneg k)

/-- Division with the constant rounded up is sound pointwise. -/
theorem holds_div {a : V → Bool} {e : CPLine V} (d : ℕ) (hd : 0 < d)
    (hdiv : ∀ v, (d : ℤ) ∣ e.1 v) (h : CPLine.Holds a e) :
    CPLine.Holds a ((fun v => e.1 v / (d : ℤ), -((-e.2) / (d : ℤ))) : CPLine V) := by
  unfold CPLine.Holds at *
  dsimp only
  have hd' : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
  have hs : (d : ℤ) * (∑ v, e.1 v / (d : ℤ) * (if a v then 1 else 0))
      = ∑ v, e.1 v * (if a v then 1 else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← mul_assoc, Int.mul_ediv_cancel' (hdiv v)]
  have hq : -(∑ v, e.1 v / (d : ℤ) * (if a v then 1 else 0)) ≤ (-e.2) / (d : ℤ) := by
    rw [Int.le_ediv_iff_mul_le hd']
    linarith
  linarith


/- Dependency counting on the 45 assignments that each witness one necessary input constraint. -/
def seen (π : List (CPLine V)) : Finset (Fin 45) :=
  (π.map bad).foldr (· ∪ ·) ∅

theorem mem_seen (π : List (CPLine V)) (i : Fin 45) :
    i ∈ seen π ↔ ∃ e ∈ π, i ∈ bad e := by
  induction π with
  | nil => simp [seen]
  | cons e π ih =>
    change (i ∈ bad e ∪ seen π ↔ ∃ f ∈ e :: π, i ∈ bad f)
    simp only [Finset.mem_union, List.mem_cons]
    simp only [exists_eq_or_imp, ih]

theorem bad_subset_seen {π : List (CPLine V)} {e : CPLine V} (he : e ∈ π) :
    bad e ⊆ seen π := by
  intro i hi
  exact (mem_seen π i).2 ⟨e, he, hi⟩

def CoverCnt (b : ℕ) (π : List (CPLine V)) : Prop :=
  ∀ W : Finset (CPLine V), (∀ e ∈ W, e ∈ π) → (W.biUnion bad).card ≤ b + W.card

theorem count_nil : CoverCnt 0 [] := by
  classical
  intro W hW
  have h : W = ∅ := by
    ext e
    constructor
    · intro he
      exact False.elim (by simpa using hW e he)
    · intro he
      exact False.elim (by simp at he)
  simp [h]

theorem count_source {b : ℕ} {π : List (CPLine V)} (z : CPLine V)
    (hz : (bad z).card ≤ 1) (h : CoverCnt b π) : CoverCnt b (z :: π) := by
  classical
  intro W hW
  by_cases hm : z ∈ W
  · let E := W.erase z
    have hE : ∀ e ∈ E, e ∈ π := by
      intro e he
      rcases List.mem_cons.mp (hW e (Finset.mem_of_mem_erase he)) with hez | heπ
      · exact False.elim ((Finset.mem_erase.mp he).1 hez)
      · exact heπ
    have hs : W.biUnion bad ⊆ bad z ∪ E.biUnion bad := by
      intro i hi
      obtain ⟨e, he, hie⟩ := Finset.mem_biUnion.mp hi
      by_cases hez : e = z
      · subst e
        exact Finset.mem_union_left _ hie
      · exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨e, Finset.mem_erase.mpr ⟨hez, he⟩, hie⟩)
    have h1 := h E hE
    have h2 := Finset.card_le_card hs
    have h3 := Finset.card_union_le (bad z) (E.biUnion bad)
    have h4 : E.card = W.card - 1 := Finset.card_erase_of_mem hm
    have h5 : 1 ≤ W.card := Finset.card_pos.mpr ⟨z, hm⟩
    omega
  · apply h W
    intro e he
    exact (List.mem_cons.mp (hW e he)).resolve_left (fun hez => hm (hez ▸ he))

theorem count_derived {b δ : ℕ} {π : List (CPLine V)} (z : CPLine V)
    (R : Finset (CPLine V)) (hR : ∀ e ∈ R, e ∈ π)
    (hz : bad z ⊆ R.biUnion bad) (hsize : R.card ≤ δ + 1)
    (h : CoverCnt b π) : CoverCnt (b + δ) (z :: π) := by
  classical
  intro W hW
  by_cases hm : z ∈ W
  · let E := W.erase z ∪ R
    have hE : ∀ e ∈ E, e ∈ π := by
      intro e he
      rcases Finset.mem_union.mp he with he | he
      · rcases List.mem_cons.mp (hW e (Finset.mem_of_mem_erase he)) with hez | heπ
        · exact False.elim ((Finset.mem_erase.mp he).1 hez)
        · exact heπ
      · exact hR e he
    have hs : W.biUnion bad ⊆ E.biUnion bad := by
      intro i hi
      obtain ⟨e, he, hie⟩ := Finset.mem_biUnion.mp hi
      by_cases hez : e = z
      · subst e
        obtain ⟨f, hf, hif⟩ := Finset.mem_biUnion.mp (hz hie)
        exact Finset.mem_biUnion.mpr ⟨f, Finset.mem_union_right _ hf, hif⟩
      · exact Finset.mem_biUnion.mpr
          ⟨e, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hez, he⟩), hie⟩
    have h1 := h E hE
    have h2 := Finset.card_le_card hs
    have h3 : E.card ≤ (W.erase z).card + R.card := Finset.card_union_le _ _
    have h4 := Finset.card_erase_of_mem hm
    have h5 : 1 ≤ W.card := Finset.card_pos.mpr ⟨z, hm⟩
    omega
  · have h1 := h W (by
      intro e he
      exact (List.mem_cons.mp (hW e he)).resolve_left (fun hez => hm (hez ▸ he)))
    omega

open scoped BigOperators

/- The fractional point x_v = 1/4 satisfies all input and Boolean axioms. -/
def relaxed (e : CPLine V) : Prop := 4 * e.2 ≤ ∑ v : V, e.1 v

theorem relaxed_pigeon : ∀ p : Fin 5, relaxed (pigeonLine p) := by
  unfold relaxed
  decide

theorem relaxed_pair : ∀ p q : Fin 5, ∀ h : Fin 4, p ≠ q → relaxed (pairLine p q h) := by
  unfold relaxed
  decide

theorem relaxed_axiom (C : Clause V) (hC : C ∈ formula) : relaxed (clauseCP C) := by
  rcases hC with ⟨p, rfl⟩ | ⟨p, q, h, hne, rfl⟩
  · change relaxed (clauseCP (pigeonClause p))
    rw [pigeon_line_eq]
    exact relaxed_pigeon p
  · change relaxed (clauseCP (pairClause p q h))
    rw [pair_line_eq p q h hne]
    exact relaxed_pair p q h hne

theorem relaxed_boolLo : ∀ v : V, relaxed ((fun u => if u = v then 1 else 0, 0) : CPLine V) := by
  unfold relaxed
  decide

theorem relaxed_boolHi : ∀ v : V, relaxed ((fun u => if u = v then -1 else 0, -1) : CPLine V) := by
  unfold relaxed
  decide

theorem relaxed_add {e e' : CPLine V} (h : relaxed e) (h' : relaxed e') :
    relaxed (e.1 + e'.1, e.2 + e'.2) := by
  unfold relaxed at *
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  linarith

def Budget (π : List (CPLine V)) : Prop :=
  ∃ a b : ℕ, a + b ≤ π.length ∧ (seen π).card ≤ a ∧ CoverCnt b π ∧
    (a + b = π.length → ∀ e ∈ π, relaxed e)

theorem budget_nil : Budget [] :=
  ⟨0, 0, by simp, by simp [seen], count_nil, by intro _ e he; simp at he⟩

theorem budget_source {π : List (CPLine V)} (z : CPLine V) (k : ℕ)
    (hk : k ≤ 1) (hz : (bad z).card ≤ k) (hl : relaxed z) (h : Budget π) : Budget (z :: π) := by
  obtain ⟨a, b, hlen, ha, hb, hlinear⟩ := h
  refine ⟨a + k, b, ?_, ?_, count_source z (hz.trans hk) hb, ?_⟩
  · simp only [List.length_cons]
    omega
  · change (bad z ∪ seen π).card ≤ a + k
    have h1 := Finset.card_union_le (bad z) (seen π)
    omega
  · intro heq e he
    simp only [List.length_cons] at heq
    have heq' : a + b = π.length := by omega
    rcases List.mem_cons.mp he with rfl | he
    · exact hl
    · exact hlinear heq' e he

theorem budget_derived {π : List (CPLine V)} (z : CPLine V) (δ : ℕ)
    (hδ : δ ≤ 1) (R : Finset (CPLine V)) (hR : ∀ e ∈ R, e ∈ π)
    (hz : bad z ⊆ R.biUnion bad) (hsize : R.card ≤ δ + 1)
    (hl : δ = 1 → (∀ e ∈ R, relaxed e) → relaxed z)
    (h : Budget π) : Budget (z :: π) := by
  obtain ⟨a, b, hlen, ha, hb, hlinear⟩ := h
  have hs : bad z ⊆ seen π := by
    intro i hi
    obtain ⟨e, he, hie⟩ := Finset.mem_biUnion.mp (hz hi)
    exact bad_subset_seen (hR e he) hie
  have heq : seen (z :: π) = seen π := by
    change bad z ∪ seen π = seen π
    exact Finset.union_eq_right.mpr hs
  refine ⟨a, b + δ, ?_, ?_, count_derived z R hR hz hsize hb, ?_⟩
  · simp only [List.length_cons]
    omega
  · rw [heq]
    exact ha
  · intro heq' e he
    simp only [List.length_cons] at heq'
    have hd : δ = 1 := by omega
    have heqold : a + b = π.length := by omega
    rcases List.mem_cons.mp he with rfl | he
    · exact hl hd (fun f hf => hlinear heqold f (hR f hf))
    · exact hlinear heqold e he

theorem bad_boolLo (v : V) : bad ((fun u => if u = v then 1 else 0, 0) : CPLine V) = ∅ := by
  ext i
  simp only [mem_bad]
  constructor
  · intro h
    exact False.elim (h (holds_boolLo (critical i) v))
  · intro h
    exact False.elim (by simp at h)

theorem bad_boolHi (v : V) : bad ((fun u => if u = v then -1 else 0, -1) : CPLine V) = ∅ := by
  ext i
  simp only [mem_bad]
  constructor
  · intro h
    exact False.elim (h (holds_boolHi (critical i) v))
  · intro h
    exact False.elim (by simp at h)

theorem bad_add (e e' : CPLine V) :
    bad (e.1 + e'.1, e.2 + e'.2) ⊆ bad e ∪ bad e' := by
  classical
  intro i hi
  apply Finset.mem_union.mpr
  by_cases he : CPLine.Holds (critical i) e
  · right
    apply (mem_bad i e').mpr
    intro he'
    exact (mem_bad i _).mp hi (holds_add he he')
  · left
    exact (mem_bad i e).mpr he

theorem bad_mul (e : CPLine V) (k : ℕ) :
    bad ((k : ℤ) • e.1, (k : ℤ) * e.2) ⊆ bad e := by
  intro i hi
  apply (mem_bad i e).mpr
  intro he
  exact (mem_bad i _).mp hi (holds_mul k he)

theorem bad_div (e : CPLine V) (d : ℕ) (hd : 0 < d) (hv : ∀ v, (d : ℤ) ∣ e.1 v) :
    bad (fun v => e.1 v / (d : ℤ), -((-e.2) / (d : ℤ))) ⊆ bad e := by
  intro i hi
  apply (mem_bad i e).mpr
  intro he
  exact (mem_bad i _).mp hi (holds_div d hd hv he)

theorem budget_of_derivation {π : List (CPLine V)} (h : IsCPDerivation formula π) : Budget π := by
  classical
  induction h with
  | nil => exact budget_nil
  | ax C _ hC ih => exact budget_source _ 1 (by decide) (axiom_bad_bound C hC) (relaxed_axiom C hC) ih
  | boolLo v _ ih => exact budget_source _ 0 (by decide) (by simp [bad_boolLo]) (relaxed_boolLo v) ih
  | boolHi v _ ih => exact budget_source _ 0 (by decide) (by simp [bad_boolHi]) (relaxed_boolHi v) ih
  | @add π e e' _ he he' ih =>
    apply budget_derived _ 1 (by decide) {e, e'} ?_ ?_ ?_ ?_ ih
    · intro f hf
      simp only [Finset.mem_insert, Finset.mem_singleton] at hf
      rcases hf with rfl | rfl
      · exact he
      · exact he'
    · simpa using bad_add e e'
    · have hh := Finset.card_insert_le e ({e'} : Finset (CPLine V))
      simpa using hh
    · intro _ hh
      exact relaxed_add (hh e (by simp)) (hh e' (by simp))
  | @mul π e k _ he ih =>
    apply budget_derived _ 0 (by decide) {e} ?_ ?_ (by simp) (by intro h; omega) ih
    · intro f hf
      have hf' := Finset.mem_singleton.mp hf
      subst f
      exact he
    · simpa using bad_mul e k
  | @div π e d _ he hd hv ih =>
    apply budget_derived _ 0 (by decide) {e} ?_ ?_ (by simp) (by intro h; omega) ih
    · intro f hf
      have hf' := Finset.mem_singleton.mp hf
      subst f
      exact he
    · simpa using bad_div e d hd hv

/- A genuine lower bound, below the still-open cutoff of 109. -/
theorem refutation_length_ge_90 {π : List (CPLine V)}
    (h : IsCPRefutation formula π) : 90 ≤ π.length := by
  classical
  obtain ⟨a, b, hlen, ha, hb, hlinear⟩ := budget_of_derivation h.1
  have hz : (bad ((0 : V → ℤ), 1)).card = 45 := by
    rw [bad_contradiction]
    simp
  have hs := Finset.card_le_card (bad_subset_seen h.2)
  rw [hz] at hs
  have hc := hb {((0 : V → ℤ), 1)} (by
    intro e he
    have he' := Finset.mem_singleton.mp he
    subst e
    exact h.2)
  simp only [Finset.singleton_biUnion, Finset.card_singleton] at hc
  rw [hz] at hc
  have hstrict : a + b < π.length := by
    by_contra hn
    have heq : a + b = π.length := by omega
    have hh := hlinear heq ((0 : V → ℤ), 1) h.2
    norm_num [relaxed] at hh
  omega

end PEqualNP.Outside.L_meta_9698

/- Original target, still open:
¬ (∃ π : List (PEqualNP.Search.CPLine (Fin (4 + 1) × Fin 4)), PEqualNP.Search.IsCPRefutation (PEqualNP.ProofComplexity.PHP (4 + 1) 4) π ∧ π.length ≤ 108)
-/
