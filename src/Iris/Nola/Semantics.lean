import Iris.BI
import Iris.Algebra.CMRA
import Iris.Algebra.OFE
import Iris.Algebra.UPred
import Iris.Algebra.IProp
import Iris.Instances.UPred.Instance
import Iris.Algebra.Own
import Iris.ProofMode

import Iris.Nola.Syntax
import Iris.Nola.Inv

section noliris
variable (FF : Iris.GFunctors)

open Iris.BI

noncomputable def cif_sem {FF} (s : @cif.{u} FF) : Iris.IProp FF :=
  match s with
  | .cifs_all A Φ => iprop(∀ (a : A), cif_sem (Φ a))
  | .cifs_ex A Φ => iprop(∃ (a : A), cif_sem (Φ a))
  | .cifs_bin s P Q => let (P, Q) := (cif_sem P, cif_sem Q);
    (match s with
    | .cifs_and => iprop(P ∧ Q) | .cifs_or => iprop(P ∨ Q)
    | .cifs_imp => iprop(P -> Q) | .cifs_wand => iprop(P -∗ Q)
    | .cifs_sep => iprop(P ∗ Q))
  | .cifs_un s P => let P := cif_sem P;
    (match s with
    | .cifs_plain => iprop(■ P) | .cifs_pers => iprop(□ P)
    | .cifs_bupd => iprop(|==> P)
    | .cifs_except0 => iprop(◇ P))
  | .cifs_pure φ => iprop(⌜φ⌝)
  | .cifs_later Φ => iprop(▷ Φ)
  | .cifs_inv N F => inv_tok N F
  | cif.cifs_own a => own a

instance cif_inhabited : Inhabited (cif FF) where
  default := cif.cifs_pure True

notation "⟦" f "⟧" => cif_sem f

-- axiom sinv_unfold {FF} p (F : cif FF) :
--   ∃ (A : Type) (_ : Iris.CMRA A) (_ : inG FF A) (a : cif FF -> A),
--   sinv_tok p F = own (a F)

-- theorem cif_sem_lift (F : cif FF) :
--   iprop(⟦ lift_cif_to F ⟧ ⊣⊢ ⟦ F ⟧) := by
--   induction F with
--   | cifs_all A Φ IH =>
--     simp [cif_sem, lift_cif_to]
--     constructor <;> iintro h <;> iintro a
--     · ispecialize h (ULift.up a); simp []; istop
--       obtain ⟨ IH, _ ⟩ := IH a
--       apply Iris.BI.entails_trans.trans Iris.BI.emp_sep.1 IH
--     · ispecialize h (a.down); istop
--       obtain ⟨ _, IH ⟩ := IH a.down
--       apply Iris.BI.entails_trans.trans Iris.BI.emp_sep.1 IH
--   | cifs_ex A Φ IH =>
--     simp [cif_sem, lift_cif_to]
--     constructor <;> iintro ⟨ a, h ⟩
--     · iexists (a.down); istop; apply (IH _).1
--     · iexists (ULift.up a); simp []; istop; apply (IH _).2
--   | cifs_bin s P Q IHP IHQ =>
--     cases s <;> simp [cif_sem, lift_cif_to]
--     · apply (Iris.BI.and_congr IHP IHQ)
--     · apply (Iris.BI.or_congr IHP IHQ)
--     · apply (Iris.BI.imp_congr IHP IHQ)
--     · apply (Iris.BI.sep_congr IHP IHQ)
--     · apply (Iris.BI.wand_congr IHP IHQ)
--   | cifs_un s P IHP =>
--     cases s <;> simp [cif_sem, lift_cif_to]
--     · constructor <;> apply Iris.BIPlainly.mono; apply IHP.1; apply IHP.2
--     · apply (Iris.BI.intuitionistically_congr IHP)
--     · constructor <;> apply Iris.BIUpdate.mono; apply IHP.1; apply IHP.2
--     · unfold Iris.BI.BIBase.except0
--       apply Iris.BI.or_congr; apply BIBase.BiEntails.rfl; apply IHP
--   | cifs_pure φ =>
--     simp [cif_sem, lift_cif_to]
--   | cifs_later iP =>
--     simp [cif_sem, lift_cif_to]
--   | cifs_inv N F IH =>
--     simp [cif_sem, lift_cif_to]
--     unfold inv_tok
--     apply Iris.BI.exists_congr; intros p
--     apply Iris.BI.sep_congr; apply BIBase.BiEntails.rfl
--     have ⟨ _, _, _, _, HF ⟩ := sinv_unfold p F
--     have ⟨ _, _, _, _, HFlift ⟩ := sinv_unfold p (lift_cif_to F)
--     rewrite [HF, HFlift]
--     sorry
--   | cifs_own a =>
--     simp [lift_cif_to]; apply BIBase.BiEntails.rfl

@[simp]
theorem cif_wandiff_sem (P Q : @cif.{u1} FF) :
  ⟦ cifs_wandiff P Q ⟧ = iprop(⟦ P ⟧ ∗-∗ ⟦ Q ⟧) := by
  simp [cifs_wandiff, cif_sem]

theorem semantic_alteration (P Q : cif FF) :
  ⊢
  □ (⟦ lift_cif_to P ⟧ ∗-∗ ⟦ lift_cif_to Q ⟧) -∗
  (⟦ cif_inv.{u} N P ⟧ -∗ ⟦ cif_inv.{u} N Q ⟧) := by
  simp [cif_sem, cif_inv]
  iintro #Hequiv ⟨ P', Hequivinv, Hinv ⟩
  iexists P'
  isplit l [Hequivinv]
  · sorry
  · iexact Hinv

end noliris
