import Iris.Nola.Syntax
import Iris.Nola.Semantics
import Iris.Nola.Notations
import Iris.Nola.Inv

inductive AProp.{u} FF : Bool -> Type _ where
| IProp (P : Iris.IProp FF) : AProp FF true
| FProp (fP : Fml.{u} FF) : AProp FF false

namespace AProp

def to_IProp : AProp FF b -> Iris.IProp FF
| IProp P => P
| FProp P => ⟦ P ⟧

def guard : AProp FF b -> AProp FF false
| IProp P => FProp fml(▷ P)
| FProp P => FProp P

def unguard : AProp FF b -> AProp FF true
| IProp P => IProp P
| FProp P => IProp ⟦ P ⟧

def to_Formula : AProp FF b -> Fml FF := fun P =>
match P.guard with
| FProp fP => fP

/- Binary connectives -/

def and {b₁ b₂} (P : AProp FF b₁) (Q : AProp FF b₂) : AProp FF (b₁ || b₂) :=
match P, Q with
| IProp P, IProp Q => IProp iprop(P ∧ Q)
| IProp P, FProp Q => IProp iprop(P ∧ ⟦Q⟧)
| FProp P , IProp Q => IProp iprop(⟦P⟧ ∧ Q)
| FProp P, FProp Q => FProp fml(P ∧ Q)

def or {b₁ b₂} (P : AProp FF b₁) (Q : AProp FF b₂) : AProp FF (b₁ || b₂) :=
match P, Q with
| IProp P, IProp Q => IProp iprop(P ∨ Q)
| IProp P, FProp Q => IProp iprop(P ∨ ⟦Q⟧)
| FProp P, IProp Q => IProp iprop(⟦P⟧ ∨ Q)
| FProp P, FProp Q => FProp fml(P ∨ Q)

def imp {b₁ b₂} (P : AProp FF b₁) (Q : AProp FF b₂) : AProp FF (b₁ || b₂) :=
match P, Q with
| IProp P, IProp Q => IProp iprop(P -> Q)
| IProp P, FProp Q => IProp iprop(P -> ⟦Q⟧)
| FProp P, IProp Q => IProp iprop(⟦P⟧ -> Q)
| FProp P, FProp Q => FProp fml(P -> Q)

def sep {b₁ b₂} (P : AProp FF b₁) (Q : AProp FF b₂) : AProp FF (b₁ || b₂) :=
match P, Q with
| IProp P, IProp Q => IProp iprop(P ∗ Q)
| IProp P, FProp Q => IProp iprop(P ∗ ⟦Q⟧)
| FProp P, IProp Q => IProp iprop(⟦P⟧ ∗ Q)
| FProp P, FProp Q => FProp fml(P ∗ Q)

def wand {b₁ b₂} (P : AProp FF b₁) (Q : AProp FF b₂) : AProp FF (b₁ || b₂) :=
match P, Q with
| IProp P, IProp Q => IProp iprop(P -∗ Q)
| IProp P, FProp Q => IProp iprop(P -∗ ⟦Q⟧)
| FProp P, IProp Q => IProp iprop(⟦P⟧ -∗ Q)
| FProp P, FProp Q => FProp fml(P -∗ Q)

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
| FProp P => FProp fml(<pers> P)

def plainly {b} : AProp FF b -> AProp FF b
| IProp P => IProp iprop(■ P)
| FProp P => FProp fml(■ P)

def later {b} : AProp FF b -> AProp FF false
| IProp P => FProp fml(▷ P)
| FProp P => FProp fml(▷ ⟦P⟧)

def bupd {b} : AProp FF b -> AProp FF b
| IProp P => IProp iprop(|==> P)
| FProp P => FProp fml(|==> P)

def pure (P : Prop) : AProp FF false :=
  FProp fml(⌜P⌝)

/- Quantifiers -/

set_option pp.universes true

def all.{u} {A : Type u} {b} (Φ : A -> AProp.{u} FF b) : AProp.{u} FF b :=
match b with
| true => IProp iprop(∀ a, (Φ a).to_IProp)
| false => FProp fml(∀ (a : A), (Φ a).to_Formula)

def impred_all.{u, v} {A : Type u} (Φ : A -> AProp.{u} FF b) : AProp.{v} FF true :=
  IProp iprop(∀ a, (Φ a).to_IProp)

def all_pred {A : Type} (Φ : A -> (∀ b, AProp FF b)) : AProp FF true :=
  IProp iprop(∀ a, (Φ a true).to_IProp)

noncomputable def sForall (Ψ : AProp FF false -> Prop) : AProp FF false :=
  FProp (Fml.sForall (fun (p : Fml FF) => Ψ (FProp p)))

def sForall' {FF} (Ψ : AProp.{u+1} FF true -> Prop) : AProp.{u+1} FF true :=
  IProp (UPred.sForall (fun P => Ψ (IProp P)))

def sForall'' {FF} (Ψ : ∀ b, AProp FF b -> Prop) : AProp FF true :=
  IProp (UPred.sForall (fun P => Ψ true (IProp P)))

noncomputable def sExists (Ψ : AProp FF false -> Prop) : AProp FF false :=
  FProp (Fml.sExists (fun (p : Fml FF) => Ψ (FProp p)))

def ex {A : Type} {b} (Φ : A -> AProp FF b) : AProp FF b :=
match b with
| true => IProp iprop(∃ a, (Φ a).to_IProp)
| false => FProp fml(∃ (a : A), (Φ a).to_Formula)

def ex_pred {A : Type} (Φ : A -> (∀ b, AProp FF b)) : AProp FF true :=
  IProp iprop(∃ a, (Φ a true).to_IProp)

def ainv_tok {b} (N : Namespace) (P : AProp FF b) : AProp FF false :=
  FProp (Fml.inv N P.to_Formula)
-- theorem ainv_tok_alloc N (P : AProp FF b) :
--   ⊢ iprop(P.to_IProp -∗ bupdw (inv_wsat) (ainv_tok N P))

end AProp
