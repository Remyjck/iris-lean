import Iris.Nola.Embedding
import Iris.BI
import Iris.Algebra.OFE

structure aProp (FF : Iris.GFunctors) where
  tag : Bool
  car : AProp FF tag

namespace aProp

def and (P Q : aProp FF) : aProp FF := ⟨ P.tag || Q.tag, AProp.and P.car Q.car ⟩
def or (P Q : aProp FF) : aProp FF := ⟨ P.tag || Q.tag, AProp.or P.car Q.car ⟩
def imp (P Q : aProp FF) : aProp FF := ⟨ P.tag || Q.tag, AProp.imp P.car Q.car ⟩
def sep (P Q : aProp FF) : aProp FF := ⟨ P.tag || Q.tag, AProp.sep P.car Q.car ⟩
def wand (P Q : aProp FF) : aProp FF := ⟨ P.tag || Q.tag, AProp.wand P.car Q.car ⟩

def persistently (P : aProp FF) : aProp FF := ⟨ P.tag, AProp.persistently P.car ⟩
def later (P : aProp FF) : aProp FF := ⟨ false, AProp.later P.car ⟩

def pure (P : Prop) : aProp FF := ⟨ false, AProp.pure P ⟩

def sForall (Ψ : aProp FF -> Prop) : aProp FF := ⟨ true, AProp.sForall (fun b p => Ψ ⟨b, p⟩) ⟩
def sExists (Ψ : aProp FF -> Prop) : aProp FF := ⟨ true, AProp.sExists (fun b p => Ψ ⟨b, p⟩) ⟩

def emp : aProp FF := pure True

def Entails (P Q : aProp FF) : Prop :=
  P.car.to_IProp ⊢ Q.car.to_IProp

/- OFE Instance -/

instance : Iris.OFE (aProp FF) where
  Equiv P Q := Iris.instOFEUPred.Equiv P.car.to_IProp Q.car.to_IProp
  Dist n P Q := Iris.instOFEUPred.Dist n P.car.to_IProp Q.car.to_IProp
  dist_eqv := {
    refl _ _ _ _ _ := .rfl
    symm H _ _ A B := (H _ _ A B).symm
    trans H1 H2 _ _ A B := (H1 _ _ A B).trans (H2 _ _ A B) }
  equiv_dist := ⟨
    fun Heqv _ _ _ _ Hvalid => Heqv _ _ Hvalid,
    fun Hdist _ _ Hvalid => Hdist _ _ _ (Nat.le_refl _) Hvalid⟩
  dist_lt Hdist Hlt _ _ Hle Hvalid :=
    Hdist _ _ (Nat.le_trans Hle (Nat.le_of_succ_le Hlt)) Hvalid

end aProp

open Iris BI

section aPropInstance

instance bi_inst : BIBase (aProp FF) where
  Entails      := aProp.Entails
  emp          := aProp.emp
  pure         := aProp.pure
  and          := aProp.and
  or           := aProp.or
  imp          := aProp.imp
  sForall      := aProp.sForall
  sExists      := aProp.sExists
  sep          := aProp.sep
  wand         := aProp.wand
  persistently := aProp.persistently
  later        := aProp.later

namespace aProp

instance entails_preorder : Std.Preorder (Entails (FF := FF)) where
  refl _ _ _ H := H
  trans H1 H2 _ _ Hv H := H2 _ _ Hv <| H1 _ _ Hv H

instance later_contractive : OFE.Contractive aProp.later (α := aProp FF) where
  distLater_dist {n x y} Hl := by
    rcases x with ⟨b₁, x⟩; rcases y with ⟨b₂, y⟩
    simp [aProp.later]
    cases x <;> cases y <;> simp_all [OFE.Dist, OFE.DistLater] <;>
    intros n' x Hleq Hvalid <;>
    have := UPred.later_contractive.distLater_dist Hl <;>
    replace this := this n' x Hleq Hvalid <;>
    apply this

theorem Entails_UPredEntails {b₁ b₂} (P : AProp FF b₁) (Q : AProp FF b₂) :
  P.to_IProp ⊣⊢ Q.to_IProp <->
  @BiEntails (aProp FF) _ { tag := b₁, car := P } { tag := b₂, car := Q } := by
  constructor <;> rintro ⟨ Pq, Qp ⟩
  · constructor <;> simp [BI.Entails, aProp.Entails] <;> assumption
  · simp_all [BI.Entails, aProp.Entails]; constructor <;> assumption

theorem Entail_UPredEntail {P Q : aProp FF} :
  P.car.to_IProp ⊢ Q.car.to_IProp <->
  aProp.Entails P Q := by
  constructor <;> simp [aProp.Entails]

theorem Dist_UPredDist {b₁ b₂} (P : AProp FF b₁) (Q : AProp FF b₂) :
  P.to_IProp ≡{n}≡ Q.to_IProp <->
  @aProp.instOFE.Dist n { tag := b₁, car := P } { tag := b₂, car := Q } := by
  constructor <;> intro HDist n x Hleq Hvalid <;> replace HDist := HDist n x Hleq Hvalid <;> simp [HDist]

theorem sForall_ne {n : Nat} {Ψ₁ Ψ₂ : aProp FF → Prop} :
  liftRel (fun x1 x2 => x1 ≡{n}≡ x2) Ψ₁ Ψ₂ →
  ∀ (n' : Nat) (x' : IResUR FF),
  n' ≤ n → ✓{n'} x' → ((sForall Ψ₁).car.to_IProp.holds n' x' ↔ (sForall Ψ₂).car.to_IProp.holds n' x') := by
  sorry

theorem sExists_ne {n : Nat} {Ψ₁ Ψ₂ : aProp FF → Prop} :
  liftRel (fun x1 x2 => x1 ≡{n}≡ x2) Ψ₁ Ψ₂ →
  ∀ (n' : Nat) (x' : IResUR FF),
  n' ≤ n → ✓{n'} x' → ((sExists Ψ₁).car.to_IProp.holds n' x' ↔ (sExists Ψ₂).car.to_IProp.holds n' x') := by
  sorry

theorem and_ne {n : Nat} {P P' : aProp FF} (H : P ≡{n}≡ P') {Q Q' : aProp FF} (H' : Q ≡{n}≡ Q') :
  iprop(P ∧ Q) ≡{n}≡ iprop(P' ∧ Q') := by
  have := UPred.instBIUPred.and_ne.ne (n := n) H H'
  simp [BI.and, aProp.and]
  apply (Dist_UPredDist _ _).1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases P' with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q' with ⟨ _, ⟨_, _⟩⟩ <;>
  simp_all [AProp.and, AProp.to_IProp]

theorem or_ne {n : Nat} {P P' : aProp FF} (H : P ≡{n}≡ P') {Q Q' : aProp FF} (H' : Q ≡{n}≡ Q') :
  iprop(P ∨ Q) ≡{n}≡ iprop(P' ∨ Q') := by
  have := UPred.instBIUPred.or_ne.ne (n := n) H H'
  simp [BI.or, aProp.or]
  apply (Dist_UPredDist _ _).1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases P' with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q' with ⟨ _, ⟨_, _⟩⟩ <;>
  simp_all [AProp.or, AProp.to_IProp]

theorem imp_ne {n : Nat} {P P' : aProp FF} (H : P ≡{n}≡ P') {Q Q' : aProp FF} (H' : Q ≡{n}≡ Q') :
  iprop(P -> Q) ≡{n}≡ iprop(P' -> Q') := by
  have := UPred.instBIUPred.imp_ne.ne (n := n) H H'
  simp [BI.imp, aProp.imp]
  apply (Dist_UPredDist _ _).1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases P' with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q' with ⟨ _, ⟨_, _⟩⟩ <;>
  simp_all [AProp.imp, AProp.to_IProp]

theorem sep_ne {n : Nat} {P P' : aProp FF} (H : P ≡{n}≡ P') {Q Q' : aProp FF} (H' : Q ≡{n}≡ Q') :
  iprop(P ∗ Q) ≡{n}≡ iprop(P' ∗ Q') := by
  have := UPred.instBIUPred.sep_ne.ne (n := n) H H'
  simp [BI.sep, aProp.sep]
  apply (Dist_UPredDist _ _).1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases P' with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q' with ⟨ _, ⟨_, _⟩⟩ <;>
  simp_all [AProp.sep, AProp.to_IProp]

theorem wand_ne {n : Nat} {P P' : aProp FF} (H : P ≡{n}≡ P') {Q Q' : aProp FF} (H' : Q ≡{n}≡ Q') :
  iprop(P -∗ Q) ≡{n}≡ iprop(P' -∗ Q') := by
  have := UPred.instBIUPred.wand_ne.ne (n := n) H H'
  simp [BI.wand, aProp.wand]
  apply (Dist_UPredDist _ _).1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases P' with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q' with ⟨ _, ⟨_, _⟩⟩ <;>
  simp_all [AProp.wand, AProp.to_IProp]

theorem persistently_ne {n : Nat} {P P' : aProp FF} (H : P ≡{n}≡ P') :
  iprop(<pers> P) ≡{n}≡ iprop(<pers> P') := by
  have := UPred.instBIUPred.persistently_ne.ne (n := n) H
  simp [BI.persistently, aProp.persistently]
  apply (Dist_UPredDist _ _).1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases P' with ⟨ _, ⟨_, _⟩⟩ <;>
  simp_all [AProp.persistently, AProp.to_IProp]

theorem and_elim_l {P Q : aProp FF} : P ∧ Q ⊢ P := by
  apply Entail_UPredEntail.1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q with ⟨ _, ⟨_, _⟩⟩ <;>
  apply UPred.instBIUPred.and_elim_l

theorem and_elim_r {P Q : aProp FF} : P ∧ Q ⊢ Q := by
  apply Entail_UPredEntail.1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q with ⟨ _, ⟨_, _⟩⟩ <;>
  apply UPred.instBIUPred.and_elim_r

theorem and_intro {P Q R : aProp FF} : (P ⊢ Q) → (P ⊢ R) → P ⊢ Q ∧ R := by
  intro H1 H2
  replace H1 := Entail_UPredEntail.2 H1;
  replace H2 := Entail_UPredEntail.2 H2
  apply Entail_UPredEntail.1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases R with ⟨ _, ⟨_, _⟩⟩ <;>
  apply UPred.instBIUPred.and_intro H1 H2

theorem or_intro_l {P Q : aProp FF} : P ⊢ P ∨ Q := by
  apply Entail_UPredEntail.1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q with ⟨ _, ⟨_, _⟩⟩ <;>
  apply UPred.instBIUPred.or_intro_l

theorem or_intro_r {P Q : aProp FF} : Q ⊢ P ∨ Q := by
  apply Entail_UPredEntail.1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q with ⟨ _, ⟨_, _⟩⟩ <;>
  apply UPred.instBIUPred.or_intro_r

theorem or_elim {P Q R : aProp FF} : (P ⊢ R) → (Q ⊢ R) → P ∨ Q ⊢ R := by
  intro H1 H2
  replace H1 := Entail_UPredEntail.2 H1;
  replace H2 := Entail_UPredEntail.2 H2
  apply Entail_UPredEntail.1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases R with ⟨ _, ⟨_, _⟩⟩ <;>
  apply UPred.instBIUPred.or_elim H1 H2

theorem imp_intro {P Q R : aProp FF} : (P ∧ Q ⊢ R) → P ⊢ Q → R := by
  intro H
  replace H := Entail_UPredEntail.2 H
  apply Entail_UPredEntail.1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases R with ⟨ _, ⟨_, _⟩⟩ <;>
  apply UPred.instBIUPred.imp_intro H

theorem imp_elim {P Q R : aProp FF} : (P ⊢ Q → R) → P ∧ Q ⊢ R := by
  intro H
  replace H := Entail_UPredEntail.2 H
  apply Entail_UPredEntail.1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases R with ⟨ _, ⟨_, _⟩⟩ <;>
  apply UPred.instBIUPred.imp_elim H

theorem sep_mono {P P' Q Q' : aProp FF} :
  (P ⊢ Q) →
  (P' ⊢ Q') →
  P ∗ P' ⊢ Q ∗ Q' := by
  intro H1 H2
  replace H1 := Entail_UPredEntail.2 H1;
  replace H2 := Entail_UPredEntail.2 H2
  apply Entail_UPredEntail.1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases P' with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q' with ⟨ _, ⟨_, _⟩⟩ <;>
  apply UPred.instBIUPred.sep_mono H1 H2

theorem sep_symm {P Q : aProp FF} : P ∗ Q ⊢ Q ∗ P := by
  apply Entail_UPredEntail.1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q with ⟨ _, ⟨_, _⟩⟩ <;>
  apply UPred.instBIUPred.sep_symm

theorem sep_assoc_l {P Q R : aProp FF} : (P ∗ Q) ∗ R ⊢ P ∗ Q ∗ R := by
  apply Entail_UPredEntail.1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases R with ⟨ _, ⟨_, _⟩⟩ <;>
  apply UPred.instBIUPred.sep_assoc_l

theorem wand_intro {P Q R : aProp FF} : (P ∗ Q ⊢ R) → P ⊢ Q -∗ R := by
  intro H; replace H := Entail_UPredEntail.2 H
  apply Entail_UPredEntail.1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases R with ⟨ _, ⟨_, _⟩⟩ <;>
  apply UPred.instBIUPred.wand_intro H

theorem wand_elim {P Q R : aProp FF} : (P ⊢ Q -∗ R) → P ∗ Q ⊢ R := by
  intro H; replace H := Entail_UPredEntail.2 H
  apply Entail_UPredEntail.1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases R with ⟨ _, ⟨_, _⟩⟩ <;>
  apply UPred.instBIUPred.wand_elim H

theorem persistently_mono {P Q : aProp FF} : (P ⊢ Q) → <pers> P ⊢ <pers> Q := by
  intro H; replace H := Entail_UPredEntail.2 H
  apply Entail_UPredEntail.1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q with ⟨ _, ⟨_, _⟩⟩ <;>
  apply UPred.instBIUPred.persistently_mono H

theorem persistently_idem_2 {P : aProp FF} : <pers> P ⊢ <pers> <pers> P := by
  apply Entail_UPredEntail.1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  apply UPred.instBIUPred.persistently_idem_2

theorem persistently_and_2 {P Q : aProp FF} : <pers> P ∧ <pers> Q ⊢ <pers> (P ∧ Q) := by
  apply Entail_UPredEntail.1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q with ⟨ _, ⟨_, _⟩⟩ <;>
  apply UPred.instBIUPred.persistently_and_2

theorem persistently_absorb_l {P Q : aProp FF} : <pers> P ∗ Q ⊢ <pers> P := by
  apply Entail_UPredEntail.1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q with ⟨ _, ⟨_, _⟩⟩ <;>
  apply UPred.instBIUPred.persistently_absorb_l

theorem persistently_and_l {P Q : aProp FF} : <pers> P ∧ Q ⊢ P ∗ Q := by
  apply Entail_UPredEntail.1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q with ⟨ _, ⟨_, _⟩⟩ <;>
  apply UPred.instBIUPred.persistently_and_l

theorem later_mono {P Q : aProp FF} : (P ⊢ Q) → later P ⊢ later Q := by
  intro H; replace H := Entail_UPredEntail.2 H
  apply Entail_UPredEntail.1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q with ⟨ _, ⟨_, _⟩⟩ <;>
  apply UPred.instBIUPred.later_mono H

theorem later_intro {P : aProp FF} : P ⊢ later P := by
  apply Entail_UPredEntail.1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  apply UPred.instBIUPred.later_intro

theorem later_sep {P Q : aProp FF} : later iprop(P ∗ Q) ⊣⊢ later P ∗ later Q := by
  apply (Entails_UPredEntails _ _).1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  rcases Q with ⟨ _, ⟨_, _⟩⟩ <;>
  apply UPred.instBIUPred.later_sep

theorem later_persistently {P : aProp FF} : later iprop(<pers> P) ⊣⊢ <pers> later P := by
  apply (Entails_UPredEntails _ _).1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  apply UPred.instBIUPred.later_persistently

theorem later_false_em {P : aProp FF} :
  later P ⊢ later iprop(False) ∨ (later iprop(False) → P) := by
  apply Entail_UPredEntail.1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  apply UPred.instBIUPred.later_false_em

end aProp

instance : BI (aProp FF) where
  entails_preorder := aProp.entails_preorder
  equiv_iff {P Q} := by
    rcases P with ⟨_, P⟩; rcases Q with ⟨_, Q⟩; constructor
    · intros Hequiv
      apply (aProp.Entails_UPredEntails _ _).1
      apply UPred.instBIUPred.equiv_iff.1; assumption
    · intros Hentails
      apply UPred.instBIUPred.equiv_iff.2
      apply (aProp.Entails_UPredEntails _ _).2 Hentails
  and_ne.ne n P P' H Q Q' H' := aProp.and_ne H H'
  or_ne.ne n P P' H Q Q' H' := aProp.or_ne H H'
  imp_ne.ne n P P' H Q Q' H' := aProp.imp_ne H H'
  sep_ne.ne n P P' H Q Q' H' := aProp.sep_ne H H'
  wand_ne.ne n P P' H Q Q' H' := aProp.wand_ne H H'
  persistently_ne.ne n P Q H := aProp.persistently_ne H
  later_ne := inferInstanceAs (OFE.NonExpansive (aProp.later))
  sForall_ne {n Ψ₁ Ψ₂} := aProp.sForall_ne
  sExists_ne {n Ψ₁ Ψ₂} := aProp.sExists_ne
  pure_intro {P ϕ} HP := UPred.instBIUPred.pure_intro HP
  pure_elim' {ϕ P} I :=
    UPred.instBIUPred.pure_elim' (fun HΦ => aProp.Entail_UPredEntail.2 (I HΦ))
  and_elim_l := aProp.and_elim_l
  and_elim_r := aProp.and_elim_r
  and_intro := aProp.and_intro
  or_intro_l := aProp.or_intro_l
  or_intro_r := aProp.or_intro_r
  or_elim := aProp.or_elim
  imp_intro := aProp.imp_intro
  imp_elim := aProp.imp_elim
  sForall_intro := sorry
  sForall_elim := sorry
  sExists_intro := sorry
  sExists_elim := sorry
  sep_mono := aProp.sep_mono
  emp_sep {P} := by
    apply (aProp.Entails_UPredEntails _ _).1;
    rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
    apply UPred.instBIUPred.emp_sep
  sep_symm := aProp.sep_symm
  sep_assoc_l := aProp.sep_assoc_l
  wand_intro := aProp.wand_intro
  wand_elim := aProp.wand_elim
  persistently_mono := aProp.persistently_mono
  persistently_idem_2 := aProp.persistently_idem_2
  persistently_emp_2 := UPred.instBIUPred.persistently_emp_2
  persistently_and_2 := aProp.persistently_and_2
  persistently_sExists_1 := sorry
  persistently_absorb_l := aProp.persistently_absorb_l
  persistently_and_l := aProp.persistently_and_l
  later_mono := aProp.later_mono
  later_intro := aProp.later_intro
  later_sForall_2 := sorry
  later_sExists_false := sorry
  later_sep := aProp.later_sep
  later_persistently := aProp.later_persistently
  later_false_em := aProp.later_false_em

end aPropInstance
