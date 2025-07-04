import Iris.BI

import Iris.Algebra.OFE
import Iris.Algebra.CMRA
import Iris.Algebra.UPred
import Iris.Algebra.IProp

namespace Iris

inductive aProp (M : Type u) [UCMRA M] : Type u where
  | AAnd : aProp M -> aProp M -> aProp M
  | AOr : aProp M -> aProp M -> aProp M
  | ASep  : aProp M -> aProp M -> aProp M
  | AImp : aProp M -> aProp M -> aProp M
  | AWand : aProp M ->  aProp M -> aProp M
  | APure : Prop -> aProp M
  | APersist : aProp M -> aProp M
  | ALater : aProp M -> aProp M
  | AOwnM : M -> aProp M

variable (M : Type) [UCMRA M]

def sforall (Ψ : aProp M -> Prop) : aProp M :=
  aProp.APure (∀ p, Ψ p)

def sexists (Ψ : aProp M -> Prop) : aProp M :=
  aProp.APure (∃ p, Ψ p)

structure AProp (M : Type) [UCMRA M] where APROP ::
  car : aProp M
  tag : Bool

instance aprop_ofe_inst : Iris.OFE (aProp M) := sorry
instance aprop_cofe_inst : IsCOFE (aProp M) where
  compl := by sorry
  conv_compl := by sorry

axiom and_ne (x y x' y' : aProp M) :
  x ≡{n}≡ x' ->
  y ≡{n}≡ y' ->
  aProp.AAnd x y ≡{n}≡ aProp.AAnd x' y'

axiom or_ne (x y x' y' : aProp M) :
  x ≡{n}≡ x' ->
  y ≡{n}≡ y' ->
  aProp.AOr x y ≡{n}≡ aProp.AOr x' y'

axiom imp_ne (x y x' y' : aProp M) :
  x ≡{n}≡ x' ->
  y ≡{n}≡ y' ->
  aProp.AImp x y ≡{n}≡ aProp.AImp x' y'

axiom sep_ne (x y x' y' : aProp M) :
  x ≡{n}≡ x' ->
  y ≡{n}≡ y' ->
  aProp.ASep x y ≡{n}≡ aProp.ASep x' y'

axiom wand_ne (x y x' y' : aProp M) :
  x ≡{n}≡ x' ->
  y ≡{n}≡ y' ->
  aProp.AWand x y ≡{n}≡ aProp.AWand x' y'

axiom pers_ne (x x' : aProp M) :
  x ≡{n}≡ x' ->
  aProp.APersist x ≡{n}≡ aProp.APersist x'

instance : OFE (AProp M) where
  Equiv x y := OFE.Equiv x.car y.car
  Dist n x y := OFE.Dist n x.car y.car
  dist_eqv {n} := by
    constructor; intros x; apply OFE.dist_eqv.refl
    intros x y; apply OFE.dist_eqv.symm
    intros x y z; apply OFE.dist_eqv.trans
  equiv_dist := OFE.equiv_dist
  dist_lt := OFE.dist_lt

def APropChain (c : Chain (AProp M)) : Chain (aProp M) where
  chain n := (c n).car
  cauchy Hle := (c.cauchy Hle)

instance : COFE (AProp M) where
  compl c := ⟨ COFE.compl (APropChain M c), true ⟩
  conv_compl {_} _ := COFE.conv_compl

axiom aentails : aProp M -> aProp M -> Prop
axiom aentails_refl (P : aProp M) : aentails M P P
axiom aentails_trans (P Q R : aProp M) : aentails M P Q -> aentails M Q R -> aentails M P R

section bidefs

variable {A : Type}
variable {O : Type} [OFE O] (o1 o2 : O)
variable (m : M)

protected def and (P Q : AProp M) : AProp M where
  car := aProp.AAnd P.car Q.car
  tag := P.tag || Q.tag

protected def or (P Q : AProp M) : AProp M where
  car := aProp.AOr P.car Q.car
  tag := P.tag || Q.tag

protected def sep (P Q : AProp M) : AProp M where
  car := aProp.ASep P.car Q.car
  tag := P.tag || Q.tag

protected def imp (P Q : AProp M) : AProp M where
  car := aProp.AImp P.car Q.car
  tag := P.tag || Q.tag

protected def wand (P Q : AProp M) : AProp M where
  car := aProp.AWand P.car Q.car
  tag := P.tag || Q.tag

protected def pure (P : Prop) : AProp M where
  car := aProp.APure P
  tag := false

protected def sForall (Ψ : AProp M -> Prop) : AProp M where
  car := aProp.APure (∀ p, Ψ p)
  tag := false

protected def sExists (Ψ : AProp M -> Prop) : AProp M where
  car := aProp.APure (∃ p, Ψ p)
  tag := false

protected def emp : AProp M where
  car := aProp.APure (True)
  tag := false

protected def persistently (P : AProp M) : AProp M where
  car := aProp.APersist P.car
  tag := P.tag

protected def later (P : AProp M) : AProp M where
  car := if P.tag then aProp.ALater P.car else P.car
  tag := false

axiom later_dist_zero [UCMRA M] x y : Iris.later M x ≡{0}≡ Iris.later M y
axiom later_dist_succ [UCMRA M] x y :
  OFE.DistLater (n + 1) x y ->
  Iris.later M x ≡{n + 1}≡ Iris.later M y

variable {aequiv : aProp M -> aProp M -> aProp M}
variable {aentails : aProp M -> aProp M -> Prop}

protected def equiv (P Q : AProp M) : AProp M where
  car := aequiv P.car Q.car
  tag := P.tag || Q.tag

protected def entails (P Q : AProp M) : Prop :=
  aentails P.car Q.car

protected def ownM (m : M) : AProp M where
  car := aProp.AOwnM m
  tag := false

-- protected def plainly : aProp M where
--   holds n _ := P n UCMRA.unit
--   mono H _ Hn := P.mono H (CMRA.incN_refl UCMRA.unit) Hn

axiom AcmraValid (m : M) : aProp M
noncomputable def cmraValid (m : M) : AProp M where
  car := AcmraValid M m
  tag := false

/-
def bupd : aProp M where
  holds n x := ∀ k yf, k ≤ n → ✓{k} (x • yf) → ∃ x', ✓{k} (x' • yf) ∧ Q k x'
  mono := sorry
-/

-- protected def emp : aProp M where
--   holds _ _ := True
--   mono _ _ _ := trivial

end bidefs

end Iris
