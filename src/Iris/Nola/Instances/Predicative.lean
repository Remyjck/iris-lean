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

protected noncomputable def sExists (Ψ : aProp FF -> Prop) : aProp FF :=
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
  simp [AProp.sForall, AProp.to_IProp, Fml.sForall, Fml.sem]
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
    · simp [OFE.Dist]; intros n' x Hle Hvalid
      constructor <;> intros HΨ
      · specialize HΨ1 (AProp.FProp (Classical.epsilon fun fp => (⊢ ⟦fp⟧ ∗-∗ P.down) ∧ Ψ₁ (AProp.FProp fp)))

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
  (∀ (p : aProp FF), Ψ p → P ⊢ p) → P ⊢ sForall Ψ := by
  intro H
  apply Entail_UPredEntail.1
  simp_all [sForall, aProp.sForall, AProp.sForall', Fml.sForall, AProp.to_IProp]
  cases P with | FProp fP
  simp [AProp.sForall, Fml.sForall, Fml.sem, Fml.imp]
  iintro iP P ⟨%HΨ1, %HΨ2⟩
  specialize H
    (AProp.FProp (Classical.epsilon fun fp => (⊢ ⟦fp⟧ ∗-∗ P.down) ∧ Ψ (AProp.FProp fp)))
    HΨ2
  replace H := Entail_UPredEntail.2 H
  simp [AProp.to_IProp] at H
  apply H

example (P : Fml FF → Prop) :
  (∀ (p : Fml FF), P p) ↔ (∀ (p : Iris.IProp FF) (fp : Fml FF), (⊢ iprop(⟦ (fp) ⟧ ∗-∗ p)) → P fp) := by
  constructor
  . simp +contextual
  . intros h fp
    replace h := h ⟦ (fp) ⟧ fp
    apply (h (Iris.BI.wandIff_refl))

theorem sForall_elim {p : aProp.{u + 1} FF} {Ψ : aProp.{u+1} FF → Prop} :
  Ψ p → sForall Ψ ⊢ p := by
  intro HΨ
  apply Entail_UPredEntail.1
  simp_all [sForall, aProp.sForall, AProp.sForall, Fml.sForall, AProp.to_IProp]
  cases p with | FProp fP
  simp [AProp.sForall, Fml.sForall, Fml.sem, Fml.imp]
  iintro H; ispecialize H (ULift.up ⟦fP⟧); simp []
  istop
  apply Iris.BI.entails_trans.trans Iris.BI.emp_sep.1
  apply Iris.BI.entails_trans.trans;
  · apply (@Iris.BI.imp_mono_l _ _ _ iprop(⌜True⌝) _)
    ipure_intro; intro _
    have he := @Classical.epsilon_spec _ fun fp => (⊢ ⟦fp⟧ ∗-∗ ⟦fP⟧) ∧ Ψ (AProp.FProp fp)
    specialize he ⟨fP, ⟨ Iris.BI.wandIff_refl, HΨ⟩⟩
    constructor <;> simp [he]
  iintro H
  apply Iris.BI.entails_trans.trans Iris.BI.true_imp.1
  have he := @Classical.epsilon_spec _ fun fp => (⊢ ⟦fp⟧ ∗-∗ ⟦fP⟧) ∧ Ψ (AProp.FProp fp)
  specialize he ⟨fP, ⟨ Iris.BI.wandIff_refl, HΨ⟩⟩
  exact (Iris.BI.wandIff_equiv he.1).1

theorem sExists_intro {Ψ : aProp FF → Prop} {p : aProp FF} :
  Ψ p → p ⊢ sExists Ψ := by
  intro HΨ
  apply Entail_UPredEntail.1
  simp_all [sExists, aProp.sExists, AProp.sExists, Fml.sExists, AProp.to_IProp]
  cases p with | FProp fP
  simp [Fml.sem]
  iintro HP
  iexists (ULift.up ⟦fP⟧); simp []
  have he := @Classical.epsilon_spec _ fun fp => (⊢ ⟦fp⟧ ∗-∗ ⟦fP⟧) ∧ Ψ (AProp.FProp fp)
  obtain ⟨H1, H2⟩ := he ⟨fP, ⟨ Iris.BI.wandIff_refl, HΨ⟩⟩
  iintro HP
  isplit r [HP]
  · ipure_intro
    simp [*]
  · istop; exact (Iris.BI.wandIff_equiv H1).2

theorem sExists_elim {Φ : aProp FF → Prop} {Q : aProp FF} :
  (∀ (p : aProp FF), Φ p → p ⊢ Q) → sExists Φ ⊢ Q := by
  intro H
  apply Entail_UPredEntail.1
  simp_all [sExists, aProp.sExists, AProp.sExists, Fml.sExists, AProp.to_IProp]
  cases Q with | FProp fP
  simp [Fml.sem]
  iintro ⟨P, ⟨⟨%_, %Hclassic⟩, H⟩⟩
  specialize H (AProp.FProp (Classical.epsilon fun fp => (⊢ ⟦fp⟧ ∗-∗ P.down) ∧ Φ (AProp.FProp fp))) Hclassic
  apply H

noncomputable def sForall_pred (P : ULift (Iris.IProp FF)) (Ψ : aProp FF -> Prop) :=
  (fun fp => (⊢ ⟦fp⟧ ∗-∗ P.down) ∧ Ψ (AProp.FProp fp))

theorem sForall_fold (Ψ : aProp FF -> Prop) :
  aProp.sForall Ψ
  =
  AProp.FProp
    (Fml.all fun p =>
      let p' := (Classical.epsilon (sForall_pred p Ψ))
      fml(⌜sForall_pred p Ψ p'⌝ -> p')) := by
  unfold aProp.sForall AProp.sForall Fml.sForall
  unfold sForall_pred
  simp []

theorem pure_imp [BI PROP] {Q P : PROP} {φ : Prop} (hφ : φ) (h : Q ⊢ P) : (⌜φ⌝ -> Q) ⊢ P :=
  let and_intro := Iris.BI.and_intro (Iris.BI.entails_preorder.refl) (Iris.BI.pure_intro hφ)
  and_intro.trans (Iris.BI.imp_elim_l.trans h)

theorem sForall_adequate {Φ : aProp FF → Prop} :
  (∀ p, ⌜Φ p⌝ → p) ⊢ (sForall Φ) := by
  simp [«forall»]
  apply sForall_intro
  intros P HΦ; cases P with | FProp fP
  simp [AProp.to_IProp, sForall]
  simp [sForall_fold]
  apply Entail_UPredEntail.1
  simp [AProp.to_IProp, Fml.sem]
  iintro H; ispecialize H (ULift.up ⟦fP⟧); istop
  apply Iris.BI.emp_sep.1.trans
  have he := @Classical.epsilon_spec _ (sForall_pred { down := ⟦fP⟧ } fun p => ∃ a, (⌜Φ a⌝ → a) ⊣⊢ p)
  specialize he (by
    exists fP; simp [sForall_pred, Iris.BI.wandIff_refl];
    exists (AProp.FProp fP);
    constructor
    · apply Entail_UPredEntail.1
      exact pure_imp HΦ (Iris.BI.entails_preorder.refl)
    · apply Entail_UPredEntail.1
      simp [AProp.to_IProp, imp, aProp.imp, BI.pure, aProp.pure, AProp.pure]; unfold AProp.imp; simp [Fml.sem]
      iintro HP %_; iexact HP
  )
  apply pure_imp he
  simp [sForall_pred] at he; replace he := he.1
  apply (Iris.BI.wandIff_equiv he).1

theorem forall_upred {α : Sort _} {Φ : α -> aProp FF} {P : aProp FF} :
  (P ⊢ (∀ a, Φ a)) -> AProp.to_IProp P ⊢ (∀ (a : α), AProp.to_IProp (Φ a)) := by
  intro H
  cases P with | FProp P
  replace H := Entail_UPredEntail.2 H
  apply H.trans
  iintro H a; istop
  apply Entail_UPredEntail.2
  simp [«forall»]
  apply sForall_elim
  refine ⟨a, ⟨entails_preorder.refl,entails_preorder.refl⟩⟩

theorem exists_upred {α : Sort _} {Φ : α -> aProp FF} {P : aProp FF} :
  (P ⊢ (∃ a, Φ a)) -> AProp.to_IProp P ⊢ (∃ (a : α), AProp.to_IProp (Φ a)) := by
  intro H
  cases P with | FProp P
  replace H := Entail_UPredEntail.2 H
  apply H.trans
  conv => lhs; simp [«exists», AProp.to_IProp]
  simp [sExists, aProp.sExists, AProp.sExists]
  iintro ⟨P, ⟨%H1, H2⟩⟩
  obtain ⟨H1, ⟨a, Ha⟩⟩ := H1
  iexists a; istop
  replace Ha := (Entails_UPredEntails _ _).2 Ha
  apply Ha.2

theorem upred_forall {α : Sort _} {Φ : α -> aProp FF} {P : aProp FF} :
  (AProp.to_IProp P ⊢ (∀ (a : α), AProp.to_IProp (Φ a))) -> (P ⊢ (∀ a, Φ a)) := by
  intro H
  cases P with | FProp P
  apply Entail_UPredEntail.1
  apply H.trans
  conv => rhs; simp [«forall», AProp.to_IProp]
  simp [sForall, aProp.sForall, AProp.sForall]
  iintro H iP ⟨%H1, ⟨a, %H2⟩⟩
  ispecialize H a; istop; apply Iris.BI.emp_sep.1.trans
  replace H2 := (Entails_UPredEntails _ _).2 H2
  apply H2.1

theorem upred_exists {α : Sort _} {Φ : α -> aProp FF} {P : aProp FF} :
  (AProp.to_IProp P ⊢ (∃ (a : α), AProp.to_IProp (Φ a))) -> (P ⊢ (∃ a, Φ a)) := by
  intro H
  cases P with | FProp P
  apply Entail_UPredEntail.1
  apply H.trans
  iintro ⟨a, Ha⟩; istop; apply Entail_UPredEntail.2
  apply sExists_intro
  exists a; refine ⟨entails_preorder.refl, entails_preorder.refl⟩

theorem to_iprop_all {α : Sort _} {Φ : α -> aProp FF} :
  AProp.to_IProp (iprop(∀ (a : α), Φ a)) ⊢ ∀ (a : α), (Φ a).to_IProp := by
  apply forall_upred
  apply entails_preorder.refl

theorem to_iprop_exists {α : Sort _} {Φ : α -> aProp FF} :
  AProp.to_IProp (iprop(∃ (a : α), Φ a)) ⊢ ∃ (a : α), (Φ a).to_IProp := by
  apply exists_upred
  apply entails_preorder.refl

theorem all_to_iprop {α : Sort _} {Φ : α -> aProp FF} :
  (∀ (a : α), (Φ a).to_IProp) ⊢ AProp.to_IProp (iprop(∀ (a : α), Φ a)) := by
  conv => rhs; simp [«forall», sForall, aProp.sForall, AProp.sForall, AProp.to_IProp]
  apply Iris.BI.sForall_intro
  rintro P ⟨a, Ha⟩
  apply Iris.BI.entails_preorder.trans _ Ha.1
  iintro H ⟨%H1, ⟨a, %H2⟩⟩
  ispecialize H a; istop; apply Iris.BI.emp_sep.1.trans
  replace H2 := (Entails_UPredEntails _ _).2 H2
  apply H2.1

theorem later_upred {P Q : aProp FF} :
  (P.to_IProp ⊢ later Q.to_IProp) <-> (P ⊢ later Q) := by
  cases Q with | FProp Q
  simp [Entails, aProp.Entails, later, aProp.later, AProp.later, AProp.to_IProp, Fml.sem]

theorem upred_later {P Q : aProp FF} :
  (later P.to_IProp ⊢ Q.to_IProp) <-> (later P ⊢ Q) := by
  cases P with | FProp P
  simp [Entails, aProp.Entails, later, aProp.later, AProp.later, AProp.to_IProp, Fml.sem]

-- theorem sForall_adequate_2 {Φ : aProp FF → Prop} :
--   (∀ p, ⌜Φ p⌝ → p) ⊣⊢ (sForall Φ) := by
--   simp [«forall»]
--   refine ⟨ sForall_adequate, ?_⟩
--   apply sForall_intro
--   rintro P ⟨Q, HQ⟩; cases P with | FProp fP; cases Q with | FProp fQ
--   apply entails_preorder.trans _ HQ.1
--   simp [AProp.to_IProp, sForall]
--   simp [sForall_fold]
--   apply Entail_UPredEntail.1
--   conv => simp [AProp.to_IProp]; rhs; simp [imp, aProp.imp, BI.pure, aProp.pure, AProp.pure]; unfold AProp.imp
--   simp [Fml.sem]
--   iintro H %HΦ; ispecialize H (ULift.up ⟦fP⟧); istop
--   apply Iris.BI.emp_sep.1.trans
--   sorry

theorem later_imp_true {φ : Prop} {a : Iris.IProp FF} : (⌜φ⌝ → later a) ⊢ later iprop(⌜φ⌝ → a) :=
  fun
  | 0, _, _, _ => trivial
  | n+1, x, Hx, H =>
    by
      simp [BI.imp, UPred.imp, later, UPred.later, BI.pure, UPred.pure]
      intros n' x' Hinc Hle Hvalid Hφ
      specialize H (n + 1) x (CMRA.inc_refl _) (Nat.le_refl _) Hx Hφ; simp [later, UPred.later] at H
      apply a.mono H (CMRA.incN_of_inc _ Hinc) Hle

theorem later_sForall_2 {Φ : aProp FF → Prop} :
  (∀ p, ⌜Φ p⌝ → later p) ⊢ later (sForall Φ) := by
  apply entails_preorder.trans _ (later_mono sForall_adequate)
  apply later_upred.1
  apply Iris.BI.entails_trans.trans _ (Iris.BI.later_mono all_to_iprop)
  apply Iris.BI.entails_trans.trans _ Iris.BI.later_forall_2
  iintro H a; istop
  apply later_upred.2
  apply sForall_elim
  exists a; simp []
  apply (Entails_UPredEntails _ _).1
  cases a with | FProp a
  simp [BI.imp, aProp.imp, AProp.to_IProp, BI.pure, aProp.pure, AProp.pure, later, aProp.later, AProp.later]
  unfold AProp.imp; simp [Fml.sem]
  constructor
  · apply later_imp_true
  · iintro H %HΦ; istop; apply Iris.BI.later_mono
    apply pure_imp HΦ Iris.BI.entails_preorder.refl

theorem sExists_adequate {Φ : aProp FF → Prop} :
  (∃ p, ⌜Φ p⌝ ∧ p) ⊢ (sExists Φ) := by
  simp [«exists»]
  apply sExists_elim
  rintro P ⟨Q, HQ⟩; cases P with | FProp fP; cases Q with | FProp fQ
  apply entails_preorder.trans HQ.2
  apply Entail_UPredEntail.1
  conv => lhs; simp [BI.and, aProp.and, AProp.to_IProp, BI.pure, aProp.pure, AProp.pure]; unfold AProp.and; simp [Fml.sem]
  iintro ⟨%HΦ, H⟩; istop
  apply (@Entail_UPredEntail _ (AProp.FProp fQ) _).2
  apply sExists_intro HΦ

theorem pure_intro {P : Prop} {ϕ : aProp FF} : P → AProp.to_IProp ϕ ⊢ ⌜P⌝ :=
  fun HP => UPred.instBIUPred.pure_intro HP

theorem persistently_upred {P Q : aProp FF} :
  (<pers> P.to_IProp ⊢ Q.to_IProp) <-> (<pers> P ⊢ Q) := by
  cases P with | FProp P
  simp [Entails, aProp.Entails, persistently, aProp.persistently, AProp.persistently, AProp.to_IProp, Fml.sem]

theorem sExists_adequate' {Φ : aProp FF → Prop} :
  (sExists Φ) ⊢ (∃ p, ⌜Φ p⌝ ∧ p) := by
  simp [«exists»]
  apply sExists_elim
  intro P HΦ
  apply sExists_intro
  exists P; constructor
  apply and_elim_r
  apply and_intro; apply pure_intro HΦ; apply entails_preorder.refl

theorem persistently_sExists_1 {Ψ : aProp FF → Prop} :
  <pers> sExists Ψ ⊢ ∃ p, ⌜Ψ p⌝ ∧ <pers> p := by
  apply entails_preorder.trans (persistently_mono sExists_adequate')
  apply persistently_upred.1
  apply Iris.BI.entails_trans.trans (Iris.BI.persistently_mono to_iprop_exists)
  apply Iris.BI.entails_trans.trans Iris.BI.persistently_exists.1
  iintro ⟨a, Ha⟩; istop
  apply persistently_upred.2
  apply sExists_intro
  exists a; simp []
  sorry

theorem false_conv : (iprop(False) : Iris.IProp FF) = AProp.to_IProp (AProp.pure (False)) := rfl

theorem later_conv (P : Iris.IProp FF) : later P = AProp.to_IProp (AProp.FProp fml(▷ P)) := rfl

theorem later_sExists_false {Φ : aProp FF → Prop} :
  later (sExists Φ) ⊢ later iprop(False) ∨ ∃ p, ⌜Φ p⌝ ∧ later p := by
  apply entails_preorder.trans (later_mono sExists_adequate')
  apply upred_later.1
  apply Iris.BI.entails_trans.trans (Iris.BI.later_mono to_iprop_exists)
  apply Iris.BI.entails_trans.trans Iris.BI.later_sExists_false
  iintro ⟨Hf | Ha⟩ <;> istop
  · rewrite [false_conv]; apply upred_later.2; apply or_intro_l
  · iintro ⟨P, ⟨⟨a, %Ha⟩, H⟩⟩; istop; rewrite [later_conv]; apply Entail_UPredEntail.2; apply entails_preorder.trans _ or_intro_r
    simp [] at Ha
    cases a with | FProp a
    simp [AProp.to_IProp, BI.and, aProp.and, BI.pure, aProp.pure, AProp.pure] at Ha
    unfold AProp.and at Ha; simp [Fml.sem] at Ha
    apply upred_exists
    iintro H; iexists (AProp.FProp a); istop
    simp [AProp.to_IProp, BI.and, aProp.and, later, aProp.later, AProp.later, BI.pure, aProp.pure, AProp.pure]
    unfold AProp.and; simp [Fml.sem]
    apply Iris.BI.entails_preorder.trans (Iris.BI.later_mono Ha.2)
    sorry

noncomputable instance : BI.{u+2} (aProp.{u+1} FF) where
  entails_preorder := entails_preorder
  equiv_iff := aProp.equiv_iff
  and_ne.ne _ _ _ H _ _ H' := aProp.and_ne H H'
  or_ne.ne _ _ _ H _ _ H' := aProp.or_ne H H'
  imp_ne.ne _ _ _ H _ _ H' := aProp.imp_ne H H'
  sep_ne.ne _ _ _ H _ _ H' := aProp.sep_ne H H'
  wand_ne.ne _ _ _ H _ _ H' := aProp.wand_ne H H'
  persistently_ne.ne _ _ _ H := aProp.persistently_ne H
  later_ne := inferInstanceAs (OFE.NonExpansive (aProp.later))
  sForall_ne := aProp.sForall_ne
  sExists_ne := aProp.sExists_ne
  pure_intro := pure_intro
  pure_elim' I := UPred.instBIUPred.pure_elim' (fun HΦ => Entail_UPredEntail.2 (I HΦ))
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
  sExists_intro := sExists_intro
  sExists_elim := sExists_elim
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
  persistently_sExists_1 := persistently_sExists_1
  persistently_absorb_l := aProp.persistently_absorb_l
  persistently_and_l := aProp.persistently_and_l
  later_mono := aProp.later_mono
  later_intro := aProp.later_intro
  later_sForall_2 := later_sForall_2
  later_sExists_false := later_sExists_false
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

theorem mono {P Q : aProp FF} : (P ⊢ Q) → ■ P ⊢ ■ Q := by
  intros H
  rcases P with ⟨b₁, ⟨_,_⟩⟩ <;> rcases Q with ⟨b₂,  ⟨_,_⟩⟩ <;>
  apply UPred.instBIPlainlyUPred.mono H

theorem plainly_upred {P Q : aProp FF} :
  (P.to_IProp ⊢ ■ Q.to_IProp) <-> P ⊢ ■ Q := by
  cases Q with | FProp Q
  simp [Entails, aProp.Entails, plainly, aProp.plainly, AProp.plainly, AProp.to_IProp, Fml.sem]

theorem plainly_sForall_2 {Φ : aProp FF → Prop} :
  (∀ p, ⌜Φ p⌝ → ■ p) ⊢ ■ sForall Φ := by
  apply entails_preorder.trans _ (mono sForall_adequate)
  apply plainly_upred.1
  apply Iris.BI.entails_trans.trans _ (Iris.BIPlainly.mono all_to_iprop)
  apply Iris.BI.entails_trans.trans _ Iris.BI.plainly_forall_2
  iintro H a; istop
  apply plainly_upred.2
  apply sForall_elim
  exists a; simp []
  constructor
  · sorry
  · apply Entail_UPredEntail.1
    cases a with | FProp a
    simp [BI.imp, aProp.imp, AProp.to_IProp, BI.pure, aProp.pure, AProp.pure, plainly, aProp.plainly, AProp.plainly]
    unfold AProp.imp; simp [Fml.sem]
    iintro H %HΦ; istop; apply Iris.BIPlainly.mono
    apply pure_imp HΦ Iris.BI.entails_preorder.refl

noncomputable instance : BIPlainly (aProp FF) where
  mono := mono
  elim_persistently {P} := by
    rcases P with ⟨b, ⟨_,_⟩⟩ <;>
    apply UPred.instBIPlainlyUPred.elim_persistently
  idem {P} := by
    rcases P with ⟨b, ⟨_,_⟩⟩ <;>
    apply UPred.instBIPlainlyUPred.idem
  plainly_sForall_2 := plainly_sForall_2
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
