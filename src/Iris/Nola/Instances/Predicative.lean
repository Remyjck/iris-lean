import Iris.Nola.Embedding
import Iris.BI
import Iris.Algebra.OFE


abbrev aProp FF := AProp FF false

instance : Nonempty (aProp FF) := ⟨AProp.pure True⟩

/- OFE Instance -/

abbrev OFEUPred {FF} := @Iris.instOFEUPred FF
abbrev COFEUPred {FF} := @Iris.instIsCOFEUPred FF

instance : Iris.OFE.{u + 1} (aProp FF) where
  Equiv P Q := Iris.instOFEUPred.Equiv P.to_IProp Q.to_IProp
  Dist n P Q := Iris.instOFEUPred.Dist n P.to_IProp Q.to_IProp
  dist_eqv := {
    refl _ := .rfl
    symm {P Q} H := H.symm
    trans {P Q R} H1 H2 := H1.trans H2 }
  equiv_dist {P Q} := OFEUPred.equiv_dist
  dist_lt {n P Q} := OFEUPred.dist_lt

instance : Iris.IsCOFE.{u + 1} (aProp.{u} FF) where
  compl := fun c => by
    have ic' : Iris.Chain (Iris.IProp FF) := ⟨ fun n => (c n).to_IProp, c.cauchy ⟩
    have fc' : Iris.Chain (Fml.{u} FF) := ⟨ fun n => (c n).to_Formula, sorry ⟩
    refine (AProp.FProp (COFEUPred.compl ic') (Fml.instIsCOFE.compl fc') ?_)
    sorry
  conv_compl {n c} := by apply COFEUPred.conv_compl

namespace aProp

variable {FF : Iris.GFunctors}

section bidefs

protected def Entails (P Q : aProp FF) : Prop :=
  P.to_IProp ⊢ Q.to_IProp

protected def pure (P : Prop) : aProp FF := AProp.pure P

protected def and (P Q : aProp FF) : aProp FF := AProp.and P Q

protected def or (P Q : aProp FF) : aProp FF :=AProp.or P Q

protected def imp (P Q : aProp FF) : aProp FF := AProp.imp P Q

protected noncomputable def sForall.{u} (Ψ : aProp.{u + 1} FF -> Prop) : aProp.{u + 1} FF :=
    AProp.sForall Ψ

noncomputable def all {α : Sort _} (P : α → aProp FF) : aProp FF := aProp.sForall (fun p => ∃ a, P a = p)

protected def sExists (Ψ : aProp FF -> Prop) : aProp FF :=
  AProp.sExists Ψ

protected def sep (P Q : aProp FF) : aProp FF :=  AProp.sep P Q

protected def wand (P Q : aProp FF) : aProp FF := AProp.wand P Q

protected def plainly (P : aProp FF) : aProp FF := AProp.plainly P

protected def persistently (P : aProp FF) : aProp FF := AProp.persistently P

protected def later (P : aProp FF) : aProp FF := AProp.later P

def bupd (P : aProp FF) : aProp FF := AProp.bupd P

protected def emp : aProp FF := aProp.pure True

end bidefs

open Iris BI

noncomputable instance aPropBase : BIBase.{u + 2} (aProp.{u+1} FF) where
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

instance entails_preorder : Std.Preorder (Entails (PROP := aProp FF)) where
  refl _ _ _ H := H
  trans H1 H2 _ _ Hv H := H2 _ _ Hv <| H1 _ _ Hv H

instance later_contractive : OFE.Contractive aProp.later (α := aProp FF) where
  distLater_dist {n x y} Hl := by
    simp [OFE.Dist]
    rcases x with ⟨b₁, x⟩; rcases y with ⟨b₂, y⟩
    simp [aProp.later]
    simp_all [OFE.Dist, OFE.DistLater]
    intros n' x Hleq Hvalid <;>
    {
      apply UPred.later_contractive.distLater_dist ?_
      apply Hleq; apply Hvalid
      simp [OFE.DistLater]; intros m Hlt
      try (replace Hl := Hl m Hlt; apply Hl)
    }

theorem Entails_UPredEntails (P Q : aProp FF) :
  P.to_IProp ⊣⊢ Q.to_IProp <->
  @BiEntails (aProp FF) _ P Q := by
  constructor <;> rintro ⟨ Pq, Qp ⟩
  · constructor <;> simp [BI.Entails, aProp.Entails] <;> assumption
  · simp_all [BI.Entails, aProp.Entails]; constructor <;> assumption

theorem Entail_UPredEntail {P Q : aProp FF} :
  P.to_IProp ⊢ Q.to_IProp <->
  aProp.Entails P Q := by
  constructor <;> simp [aProp.Entails]

theorem Dist_UPredDist (P Q : aProp FF) :
  P.to_IProp ≡{n}≡ Q.to_IProp <->
  Iris.OFE.Dist (α := aProp FF) n P Q := by
  simp only [OFE.Dist]

namespace aProp

theorem sForall_ne {n : Nat} {Ψ₁ Ψ₂ : aProp FF → Prop} :
  liftRel (fun x1 x2 => x1 ≡{n}≡ x2) Ψ₁ Ψ₂ →
  ∀ (n' : Nat) (x' : IResUR FF),
  n' ≤ n → ✓{n'} x' → ((sForall Ψ₁).to_IProp.holds n' x' ↔ (sForall Ψ₂).to_IProp.holds n' x') := by
  intros Hliftrel
  simp [BI.sForall, aProp.sForall]
  apply (Dist_UPredDist _ _).1
  simp [AProp.sForall, AProp.to_IProp, AProp.Fml.sForall, Fml.sem]
  apply UPred.instBIUPred.sForall_ne
  simp_all [liftRel, AProp.of_Formula]
  rcases Hliftrel with ⟨HΨ1, HΨ2⟩
  constructor
  · intros P
    exists iprop(⌜(⊢ ⟦(Classical.epsilon fun fp => (⊢ ⟦fp⟧ ∗-∗ P.down) ∧ Ψ₂ (AProp.of_Formula fp))⟧ ∗-∗ P.down) ∧
                Ψ₂ (AProp.of_Formula (Classical.epsilon fun fp => (⊢ ⟦fp⟧ ∗-∗ P.down) ∧ Ψ₂ (AProp.of_Formula fp)))⌝ →
            ⟦(Classical.epsilon fun fp => (⊢ ⟦fp⟧ ∗-∗ P.down) ∧ Ψ₂ (AProp.of_Formula fp))⟧)
    constructor
    · exists P
    · sorry
  · sorry

theorem sExists_ne {n : Nat} {Ψ₁ Ψ₂ : aProp FF → Prop} :
  liftRel (fun x1 x2 => x1 ≡{n}≡ x2) Ψ₁ Ψ₂ →
  ∀ (n' : Nat) (x' : IResUR FF),
  n' ≤ n → ✓{n'} x' → ((sExists Ψ₁).to_IProp.holds n' x' ↔ (sExists Ψ₂).to_IProp.holds n' x') := by
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

theorem emp_sep {P : aProp FF} : aProp.emp.sep P ⊣⊢ P := by
  apply (Entails_UPredEntails _ _).1
  rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
  apply UPred.instBIUPred.emp_sep

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

theorem persistently_emp_2 : (emp : aProp FF) ⊢ <pers> emp := by
  apply Entail_UPredEntail.1
  apply UPred.instBIUPred.persistently_emp_2

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

theorem equiv_iff {P Q : aProp FF} :
  P ≡ Q ↔ P ⊣⊢ Q := by
  rcases P with ⟨_, P⟩; rcases Q with ⟨_, Q⟩; constructor
  · intros Hequiv
    apply (Entails_UPredEntails _ _).1
    apply UPred.instBIUPred.equiv_iff.1; assumption
  · intros Hentails
    apply UPred.instBIUPred.equiv_iff.2
    simp [AProp.to_IProp]
    apply (Entails_UPredEntails _ _).2 Hentails

theorem sForall_intro {P : aProp FF} {Ψ : aProp FF → Prop} :
  (∀ (p : aProp FF), Ψ p → P ⊢ p) → P ⊢ sForall.{u + 2} Ψ := by
  intro H
  apply Entail_UPredEntail.1
  simp_all [sForall, aProp.sForall, AProp.sForall', Fml.sForall, AProp.to_IProp]
  cases P with | FProp fP
  simp [AProp.sForall, AProp.Fml.sForall, Fml.sem, Fml.imp]
  iintro iP P ⟨%HΨ1, %HΨ2⟩
  specialize H
    (AProp.of_Formula (Classical.epsilon fun fp => (⊢ ⟦fp⟧ ∗-∗ P.down) ∧ Ψ (AProp.of_Formula fp)))
    HΨ2
  replace H := Entail_UPredEntail.2 H
  simp [AProp.to_IProp, AProp.of_Formula] at H
  apply H

example (P : Fml FF → Prop) :
  (∀ (p : Fml FF), P p) ↔ (∀ (p : Iris.IProp FF) (fp : Fml FF), (⊢ iprop(⟦ (fp) ⟧ ∗-∗ p)) → P fp) := by
  constructor
  . simp +contextual
  . intros h fp
    replace h := h ⟦ (fp) ⟧ fp
    apply (h (Iris.BI.wandIff_refl))

theorem sForall_elim {p : aProp.{u + 1} FF} {Ψ : aProp.{u+1} FF → Prop} :
  Ψ p → sForall.{u + 2} Ψ ⊢ p := by
  intro HΨ
  apply Entail_UPredEntail.1
  simp_all [sForall, aProp.sForall, AProp.sForall, Fml.sForall, AProp.to_IProp]
  cases p with | FProp fP
  simp [AProp.sForall, AProp.Fml.sForall, Fml.sem, Fml.imp]
  iintro H; ispecialize H (ULift.up ⟦fP⟧); simp []
  istop
  apply Iris.BI.entails_trans.trans Iris.BI.emp_sep.1
  apply Iris.BI.entails_trans.trans;
  · apply (@Iris.BI.imp_mono_l _ _ _ iprop(⌜True⌝) _)
    ipure_intro; intro _
    have he := @Classical.epsilon_spec _ fun fp => (⊢ ⟦fp⟧ ∗-∗ ⟦fP⟧) ∧ Ψ (AProp.FProp fp)
    specialize he ⟨fP, ⟨ Iris.BI.wandIff_refl, HΨ⟩⟩
    constructor <;> simp [AProp.of_Formula, he]
  iintro H
  apply Iris.BI.entails_trans.trans Iris.BI.true_imp.1
  have he := @Classical.epsilon_spec _ fun fp => (⊢ ⟦fp⟧ ∗-∗ ⟦fP⟧) ∧ Ψ (AProp.of_Formula fp)
  specialize he ⟨fP, ⟨ Iris.BI.wandIff_refl, HΨ⟩⟩
  exact (Iris.BI.wandIff_equiv he.1).1

noncomputable instance : BI.{u+2} (aProp.{u+1} FF) where
  entails_preorder := entails_preorder
  equiv_iff {P Q} := aProp.equiv_iff
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
    UPred.instBIUPred.pure_elim' (fun HΦ => Entail_UPredEntail.2 (I HΦ))
  and_elim_l := aProp.and_elim_l
  and_elim_r := aProp.and_elim_r
  and_intro := aProp.and_intro
  or_intro_l := aProp.or_intro_l
  or_intro_r := aProp.or_intro_r
  or_elim := aProp.or_elim
  imp_intro := aProp.imp_intro
  imp_elim := aProp.imp_elim
  sForall_intro := sForall_intro
  sForall_elim := sForall_elim
  sExists_intro := sorry
  sExists_elim := sorry
  sep_mono := aProp.sep_mono
  emp_sep := aProp.emp_sep
  sep_symm := aProp.sep_symm
  sep_assoc_l := aProp.sep_assoc_l
  wand_intro := aProp.wand_intro
  wand_elim := aProp.wand_elim
  persistently_mono := aProp.persistently_mono
  persistently_idem_2 := aProp.persistently_idem_2
  persistently_emp_2 := aProp.persistently_emp_2
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

instance : BILaterContractive (aProp FF) where
  toContractive := later_contractive

instance (P : aProp FF) : Affine P where
  affine := by
    apply Entail_UPredEntail.1
    rcases P with ⟨ _, ⟨_, _⟩⟩ <;>
    apply UPred.instBIUPred.affine

instance : OFE.NonExpansive (bupd : aProp FF -> aProp FF) where
  ne := by
    intros n P Q H
    rcases P with ⟨b₁, ⟨_,_⟩⟩ <;> rcases Q with ⟨b₂,  ⟨_,_⟩⟩ <;>
    simp [bupd, OFE.Dist] <;>
    apply UPred.instNonExpansiveUPredBupd.ne (n := n) H

instance : Plainly (aProp FF) := ⟨aProp.plainly⟩

instance : OFE.NonExpansive (plainly : aProp FF -> aProp FF) where
  ne := by
    intros n P Q H
    rcases P with ⟨b₁, ⟨_,_⟩⟩ <;> rcases Q with ⟨b₂,  ⟨_,_⟩⟩ <;>
    simp [aProp.plainly, OFE.Dist] <;>
    apply UPred.instNonExpansiveUPredPlainly.ne (n := n) H

noncomputable instance : BIPlainly (aProp FF) where
  mono := by
    intros P Q H
    rcases P with ⟨b₁, ⟨_,_⟩⟩ <;> rcases Q with ⟨b₂,  ⟨_,_⟩⟩ <;>
    apply UPred.instBIPlainlyUPred.mono H
  elim_persistently {P} := by
    rcases P with ⟨b, ⟨_,_⟩⟩ <;>
    apply UPred.instBIPlainlyUPred.elim_persistently
  idem {P} := by
    rcases P with ⟨b, ⟨_,_⟩⟩ <;>
    apply UPred.instBIPlainlyUPred.idem
  plainly_sForall_2 := sorry
  plainly_impl_plainly := by
    intros P Q H
    rcases P with ⟨b₁, ⟨_,_⟩⟩ <;> rcases Q with ⟨b₂,  ⟨_,_⟩⟩ <;>
    apply UPred.instBIPlainlyUPred.plainly_impl_plainly H
  emp_intro _ _ _ _ := trivial
  plainly_absorb := sep_elim_l
  later_plainly := by
    intros P
    rcases P with ⟨b₁, ⟨_,_⟩⟩ <;>
    simp [BI.later, aProp.later, AProp.later, plainly, aProp.plainly, AProp.plainly] <;>
    apply (Entails_UPredEntails _ _).1
    apply UPred.instBIPlainlyUPred.later_plainly

instance : BUpd (aProp FF) := ⟨bupd⟩

end aProp
