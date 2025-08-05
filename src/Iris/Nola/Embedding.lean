import Iris.Nola.Syntax
import Iris.Nola.Semantics
import Iris.Nola.Notations
import Iris.Nola.Inv

inductive AProp.{u} FF : Bool -> Type _ where
| IProp (P : Iris.IProp FF) : AProp FF true
| FProp (iP : Iris.IProp FF) (fP : cif.{u} FF) :
  (⊢ iprop(⟦ (fP) ⟧ ∗-∗ iP)) ->
  AProp FF false

namespace AProp

def to_IProp : AProp FF b -> Iris.IProp FF
| IProp P => P
| FProp P _ _ => P

def guard : AProp FF b -> AProp FF false
| IProp P => FProp iprop(▷ P) cif(▷ P) (by apply Iris.BI.wandIff_refl)
| FProp iP fP HP => FProp iP fP HP

def unguard : AProp FF b -> AProp FF true
| IProp P | FProp P _ _ => IProp P

def to_Formula : AProp FF b -> cif FF := fun P =>
match P.guard with
| FProp _ fP _ => fP

def of_Formula (F : cif.{u} FF) : AProp.{u} FF false :=
  FProp iprop(⟦ F ⟧) F (Iris.BI.wandIff_refl)

/- Binary connectives -/

def and {b₁ b₂} (P : AProp FF b₁) (Q : AProp FF b₂) : AProp FF (b₁ || b₂) :=
match P, Q with
| IProp P, IProp Q => IProp iprop(P ∧ Q)
| IProp P, FProp iQ _ _ => IProp iprop(P ∧ iQ)
| FProp iP _ _, IProp Q => IProp iprop(iP ∧ Q)
| FProp iP fP HP, FProp iQ fQ HQ => FProp iprop(iP ∧ iQ) cif(fP ∧ fQ)
  (by
    simp [cif.sem, cif.and]
    apply Iris.BI.equiv_wandIff
    apply (Iris.BI.and_congr (Iris.BI.wandIff_equiv HP) (Iris.BI.wandIff_equiv HQ)))

def or {b₁ b₂} (P : AProp FF b₁) (Q : AProp FF b₂) : AProp FF (b₁ || b₂) :=
match P, Q with
| IProp P, IProp Q => IProp iprop(P ∨ Q)
| IProp P, FProp iQ _ _ => IProp iprop(P ∨ iQ)
| FProp iP _ _, IProp Q => IProp iprop(iP ∨ Q)
| FProp iP fP HP, FProp iQ fQ HQ => FProp iprop(iP ∨ iQ) cif(fP ∨ fQ)
  (by
    simp [cif.sem, cif.or]
    apply Iris.BI.equiv_wandIff
    apply (Iris.BI.or_congr (Iris.BI.wandIff_equiv HP) (Iris.BI.wandIff_equiv HQ)))

def imp {b₁ b₂} (P : AProp FF b₁) (Q : AProp FF b₂) : AProp FF (b₁ || b₂) :=
match P, Q with
| IProp P, IProp Q => IProp iprop(P -> Q)
| IProp P, FProp iQ _ _ => IProp iprop(P -> iQ)
| FProp iP _ _, IProp Q => IProp iprop(iP -> Q)
| FProp iP fP HP, FProp iQ fQ HQ => FProp iprop(iP -> iQ) cif(fP -> fQ)
  (by
    simp [cif.sem, cif.imp]
    apply Iris.BI.equiv_wandIff
    apply (Iris.BI.imp_congr (Iris.BI.wandIff_equiv HP) (Iris.BI.wandIff_equiv HQ)))

def sep {b₁ b₂} (P : AProp FF b₁) (Q : AProp FF b₂) : AProp FF (b₁ || b₂) :=
match P, Q with
| IProp P, IProp Q => IProp iprop(P ∗ Q)
| IProp P, FProp iQ _ _ => IProp iprop(P ∗ iQ)
| FProp iP _ _, IProp Q => IProp iprop(iP ∗ Q)
| FProp iP fP HP, FProp iQ fQ HQ => FProp iprop(iP ∗ iQ) cif(fP ∗ fQ)
  (by
    simp [cif.sem, cif.sep]
    apply Iris.BI.equiv_wandIff
    apply (Iris.BI.sep_congr (Iris.BI.wandIff_equiv HP) (Iris.BI.wandIff_equiv HQ)))

def wand {b₁ b₂} (P : AProp FF b₁) (Q : AProp FF b₂) : AProp FF (b₁ || b₂) :=
match P, Q with
| IProp P, IProp Q => IProp iprop(P -∗ Q)
| IProp P, FProp iQ _ _ => IProp iprop(P -∗ iQ)
| FProp iP _ _, IProp Q => IProp iprop(iP -∗ Q)
| FProp iP fP HP, FProp iQ fQ HQ => FProp iprop(iP -∗ iQ) cif(fP -∗ fQ)
  (by
    simp [cif.sem, cif.wand]
    apply Iris.BI.equiv_wandIff
    apply (Iris.BI.wand_congr (Iris.BI.wandIff_equiv HP) (Iris.BI.wandIff_equiv HQ)))

theorem wandIff_all (A : Type) (P Q : A -> Iris.IProp FF) :
  (∀ (a : A), ⊢ iprop(P a ∗-∗ Q a)) ->
  ⊢ iprop((∀ a, P a) ∗-∗ (∀ a, Q a)) := by
  intros Hall
  unfold Iris.BI.wandIff; isplit <;>
  iintro HP a <;> ispecialize HP a <;> istop <;>
  apply (Iris.BI.entails_trans.trans (Iris.BI.emp_sep.1)) <;>
  replace Hall := Iris.BI.wandIff_equiv (Hall a)
  · apply Hall.1
  · apply Hall.2

theorem wandIff_ex (A : Type) (P Q : A -> Iris.IProp FF) :
  (∀ (a : A), ⊢ iprop(P a ∗-∗ Q a)) ->
  ⊢ iprop((∃ a, P a) ∗-∗ (∃ a, Q a)) := by
  intros Hall
  unfold Iris.BI.wandIff; isplit <;>
  iintro ⟨a, HP⟩ <;> iexists a <;> istop <;>
  replace Hall := Iris.BI.wandIff_equiv (Hall a)
  · apply Hall.1
  · apply Hall.2

/- Unary Connectives -/

def persistently {b} : AProp FF b -> AProp FF b
| IProp P => IProp iprop(<pers> P)
| FProp iP fP HP => FProp iprop(<pers> iP) cif(<pers> fP)
  (by
    simp [cif.sem, cif.pers]
    apply Iris.BI.equiv_wandIff
    apply Iris.BI.persistently_congr
    apply Iris.BI.wandIff_equiv HP)

def later {b} : AProp FF b -> AProp FF false
| IProp P => FProp iprop(▷ P) cif(▷ P) (by apply Iris.BI.wandIff_refl)
| FProp iP fP HP => FProp iprop(▷ iP) cif(▷ iP) (by apply Iris.BI.wandIff_refl)

def pure (P : Prop) : AProp FF false :=
  FProp iprop(⌜P⌝) cif(⌜P⌝) (by apply Iris.BI.wandIff_refl)

/- Quantifiers -/

def all {A : Type} {b} (Φ : A -> AProp FF b) : AProp FF b :=
match b with
| true => IProp iprop(∀ a, (Φ a).to_IProp)
| false => FProp iprop(∀ a, (Φ a).to_IProp) cif(∀ a, (Φ a).to_Formula)
  (by
    simp [cif.sem]; unfold Iris.BI.wandIff
    apply wandIff_all; intro a
    rcases (Φ a) with _ | ⟨ iP, fP, HP ⟩; simp [to_Formula, to_IProp]; exact HP )

def all_pred {A : Type} (Φ : A -> (∀ b, AProp FF b)) : AProp FF true :=
  IProp iprop(∀ a, (Φ a true).to_IProp)

def sForall (Ψ : AProp.{u+1} FF false -> Prop) : AProp.{u+1} FF false :=
  FProp
    iprop(∀ (p : cif.{u} FF), ⌜Ψ (AProp.of_Formula (liftCif.{u,u+1} p))⌝ → ⟦ p ⟧)
    (cif.sForall.{u} (fun (p : cif.{u} FF) => Ψ (AProp.of_Formula (liftCif.{u,u+1} p))))
    (by
      simp [cif.sem, cif.sForall, cif.imp]
      apply Iris.BI.equiv_wandIff
      constructor <;> iintro H P HΨ
      · ispecialize H P HΨ
        istop; apply Iris.BI.entails_trans.trans Iris.BI.emp_sep.1
        apply (cif.sem_lift _ _).1
      · ispecialize H P HΨ
        istop; apply Iris.BI.entails_trans.trans Iris.BI.emp_sep.1
        apply (cif.sem_lift _ _).2)

def sExists (Ψ : AProp.{u+1} FF false -> Prop) : AProp.{u+1} FF false :=
  FProp
    iprop(∃ (p : cif.{u} FF), ⌜Ψ (AProp.of_Formula (liftCif.{u,u+1} p))⌝ ∧ ⟦ p ⟧)
    (cif.sExists.{u} (fun (p : cif.{u} FF) => Ψ (AProp.of_Formula (liftCif.{u,u+1} p))))
    (by
      simp [cif.sem, cif.sExists, cif.and]
      apply Iris.BI.equiv_wandIff
      apply Iris.BI.exists_congr
      intro p
      apply Iris.BI.and_congr_r
      apply cif.sem_lift)

def ex {A : Type} {b} (Φ : A -> AProp FF b) : AProp FF b :=
match b with
| true => IProp iprop(∃ a, (Φ a).to_IProp)
| false => FProp iprop(∃ a, (Φ a).to_IProp) cif(∃ (a : A), (Φ a).to_Formula)
  (by
    simp [cif.sem]; unfold Iris.BI.wandIff
    apply wandIff_ex; intro a
    rcases (Φ a) with _ | ⟨ iP, fP, HP ⟩; simp [to_Formula, to_IProp]; exact HP )

def ex_pred {A : Type} (Φ : A -> (∀ b, AProp FF b)) : AProp FF true :=
  IProp iprop(∃ a, (Φ a true).to_IProp)

def ainv_tok {b} (N : Namespace) (P : AProp FF b) : AProp FF false :=
  FProp (inv_tok N P.to_Formula) (cif.inv N P.to_Formula) (by apply Iris.BI.wandIff_refl)

-- theorem ainv_tok_alloc N (P : AProp FF b) :
--   ⊢ iprop(P.to_IProp -∗ bupdw (inv_wsat) (ainv_tok N P))

end AProp
