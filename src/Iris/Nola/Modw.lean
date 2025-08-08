import Iris.BI.BI
import Iris.BI.Extensions
import Iris.BI.Classes
import Iris.ProofMode
import Iris.Std.CoPset
import Iris.BI.Updates

/- Modality with a custom world satisfaction -/

namespace Iris.BI
open Iris.Std Iris.BI

/-- World satisfaction inclusion -/

class WsatIncl {PROP} [BI PROP] (W W' Wr : PROP) : Prop where
  wsat_incl : iprop(W ⊣⊢ W' ∗ Wr)

section wsat_incl

  instance wsat_incl_refl [BI PROP] {W} : WsatIncl W W iprop(emp : PROP) where
    wsat_incl := ProofMode.sep_emp_rev

  instance wsat_incl_emp [BI PROP] {W} : WsatIncl W iprop(emp : PROP) W where
    wsat_incl := ProofMode.emp_sep_rev

  instance wsat_incl_True [BI PROP] [BIAffine PROP] {W} : WsatIncl W iprop(True : PROP) W where
    wsat_incl := ⟨ true_sep_2, sep_elim_r ⟩

  instance wsat_incl_sep_in [BI PROP] {W W'1 W'2 Wr Wr'} :
    WsatIncl W W'1 Wr → WsatIncl Wr W'2 Wr' → WsatIncl W iprop(W'1 ∗ W'2 : PROP) Wr' := by
    rintro ⟨ Hincl1 ⟩ ⟨ Hincl2 ⟩; constructor; constructor
    · apply entails_trans.trans Hincl1.1
      apply entails_trans.trans (sep_mono_r Hincl2.1)
      apply sep_assoc.2
    · apply entails_trans.trans sep_assoc.1
      apply (entails_trans.trans _ Hincl1.2)
      apply (sep_mono_r Hincl2.2)

  instance wsat_incl_in_sep_l [BI PROP] {W1 W2 W' Wr} :
    WsatIncl W1 W' Wr → WsatIncl iprop(W1 ∗ W2 : PROP) W' iprop(Wr ∗ W2 : PROP) := by
    rintro ⟨ Hincl ⟩; constructor
    apply BIBase.BiEntails.trans (sep_congr_l Hincl)
    apply sep_assoc

  instance wsat_incl_in_sep_r [BI PROP] {W1 W2 W' Wr} :
    WsatIncl W2 W' Wr → WsatIncl iprop(W1 ∗ W2 : PROP) W' iprop(W1 ∗ Wr : PROP) := by
    rintro ⟨ Hincl ⟩; constructor
    apply BIBase.BiEntails.trans (sep_congr_r Hincl)
    apply sep_left_comm

end wsat_incl

/-- Modality with a world satisfaction -/

def modw [BI PROP] (M : PROP → PROP) (W P : PROP) : PROP :=
  iprop(W -∗ M iprop(W ∗ P))

/-- Just with a world satisfaction -/
abbrev idw [BI PROP] := (@modw PROP _ id)
abbrev idw0 [BI PROP] := (@modw PROP _ BIBase.except0)
/-- Basic update with a world satisfaction -/
abbrev bupdw [BI PROP] [BUpd PROP] := (@modw PROP _ bupd)
/-- [relax_0]: Relax modality with [◇] -/
def relax0 [BI PROP] (M : PROP → PROP) (P : PROP) : PROP := M (BIBase.except0 P)
abbrev bupd0 [BI PROP] [BUpd PROP] := (@relax0 PROP _ bupd)
abbrev bupdw0 [BI PROP] [BUpd PROP] := (@modw PROP _ bupd0)
/-- Fancy update with a world satisfaction -/
abbrev fupdw E E' [BI PROP] [FUpd PROP] := (modw (@fupd PROP _ E E'))

namespace ModwNotation
/- Notation for [modw] -/

notation "|->["W"] " P => idw W P
notation P " -∗["W"] " Q => iprop(P -∗ idw W Q)

notation "|->["W"]◇ " P => idw0 W P
notation P " -∗["W"]◇ " Q => iprop(P -∗ idw0 W Q)

notation "|=["W"]=> " P => bupdw W P
notation P " =["W"]=∗ " Q => iprop(P -∗ bupdw W Q)

notation "|=["W"]=>◇ " P => bupdw0 W P
notation P " =["W"]=∗◇ " Q => iprop(P -∗ bupdw0 W Q)

notation "|=["W"]{"E", "E'"}=> " P => fupdw E E' W P
notation "|=["W"]{"E"}=> " P => fupdw E E W P

notation P " =["W"]{"E"," E'"}=∗ " Q => iprop(P -∗ fupdw E E' W Q)
notation P " =["W"]{"E"}=∗ " Q => iprop(P -∗ fupdw E E W Q)

/- We move the position of [▷] to make the notation work -/
notation "|=["W"]{"E"}▷["E'"]=> " P => fupdw E E' W iprop(▷ (fupdw E' E W P))
notation "|=["W"]{"E"}▷=> " P => fupdw E E W iprop(▷ (fupdw E E W P))

notation "|=["W"]{"E"}▷["E'"]=>^" n:9 P:200 => Nat.iter n (λ Q => fupdw E E' W iprop(▷ (fupdw E' E W Q))) P
notation "|=["W"]{"E"}▷=>^" n:9 P:200 => Nat.iter n (λ Q => fupdw E E W iprop(▷ (fupdw E E W Q))) P

end ModwNotation
open ModwNotation

/- theorems on [modw] -/

namespace modw

end modw

/- theorems on [bupdw] -/
namespace bupdw

/-- Modify the world satisfaction of [bupdw] -/
theorem bupdw_incl_bupd [BI PROP] [BIUpdate PROP] {W W' P : PROP} :
  ⊢ iprop((W ==∗ W' ∗ (W' ==∗ W)) -∗ (|=[W']=> P) =[W]=∗ P) := by
  simp [bupdw, modw]
  iintro f P' W; istop
  apply entails_trans.trans _ (bupd_idem.1)
  apply entails_trans.trans (sep_comm.1)
  apply entails_trans.trans (sep_assoc.2)
  apply entails_trans.trans; apply sep_mono_l; apply wand_elim_r
  apply entails_trans.trans (BIUpdate.frame_r)
  apply BIUpdate.mono
  apply entails_trans.trans (sep_assoc.1)
  apply entails_trans.trans (sep_comm.1)
  apply entails_trans.trans (sep_assoc.1)
  apply entails_trans.trans; apply sep_mono_r; apply wand_elim_l
  apply entails_trans.trans _ (bupd_idem.1)
  apply entails_trans.trans (bupd_frame_l)
  apply BIUpdate.mono
  apply entails_trans.trans (sep_assoc.2)
  apply entails_trans.trans; apply sep_mono_l; apply wand_elim_l
  apply entails_trans.trans (BIUpdate.frame_r)
  exact BIBase.Entails.rfl

theorem bupdw_incl [BI PROP] [BIUpdate PROP] [w : WsatIncl W W' Wr] {P : PROP} :
  (|=[W']=> P) ⊢ |=[W]=> P := by
  simp [bupdw, modw]; rcases w with ⟨ w ⟩;
  iintro HW' HW; istop
  apply entails_trans.trans (sep_mono_r w.1)
  apply entails_trans.trans (sep_assoc.2)
  apply entails_trans.trans (sep_mono_l wand_elim_l)
  apply entails_trans.trans (BIUpdate.frame_r)
  apply BIUpdate.mono
  iintro ⟨⟨HW', HP⟩, _⟩
  isplit r [HP]
  · apply entails_trans.trans w.2; exact BIBase.Entails.rfl
  · exact BIBase.Entails.rfl

/-- [modw] over [bupdw] -/
theorem modw_bupdw [BI PROP] [BIUpdate PROP] {W W' P : PROP} :
  modw (bupdw W) W' P ⊣⊢ |=[iprop(W ∗ W')]=> P := by sorry

end bupdw

/- theorems on [bupdw_0] -/
namespace bupdw0

/-- Modify the world satisfaction of [bupdw_0] -/
theorem bupdw_0_incl_bupd [BI PROP] [BIUpdate PROP] {W W' P : PROP} :
  ⊢ (W ==∗◇ W' ∗ (W' ==∗◇ W)) -∗ (|=[W']=>◇ P) =[W]=∗◇ P := by
  simp [bupdw, modw]
  iintro f P' W; ispecialize f W; istop
  apply entails_trans.trans (bupd_frame_l)
  apply entails_trans.trans _ (bupd_idem.1)
  apply BIUpdate.mono
  iintro ⟨ Hw, ⟨Hw', Himp⟩⟩
  unfold BI.BIBase.except0
  icases Hw' with ⟨ HF | Hw' ⟩
  · apply entails_trans.trans BIUpdate.intro
    apply BIUpdate.mono
    iintro ⟨ _, HF ⟩; ileft; iexact HF
  · ispecialize Hw Hw'
    simp [bupd0, relax0]
    apply entails_trans.trans (bupd_frame_l)
    apply entails_trans.trans _ (bupd_idem.1)
    apply BIUpdate.mono
    iintro ⟨ Himp, Hw' ⟩
    unfold BI.BIBase.except0
    icases Hw' with ⟨ HF | ⟨Hw', Hp⟩ ⟩
    · apply entails_trans.trans (BIUpdate.intro)
      apply BIUpdate.mono
      iintro ⟨ _, HF ⟩; ileft; iexact HF
    · ispecialize Himp Hw'
      apply entails_trans.trans (bupd_frame_l)
      apply BIUpdate.mono
      iintro ⟨ HP, HW ⟩
      icases HW with ⟨ HF | HW ⟩
      · ileft; iexact HF
      · iright; isplit l [HW] <;> iassumption

theorem bupdw0_incl [BI PROP] [BIUpdate PROP] [WsatIncl W W' Wr] {P : PROP} :
  (|=[W']=>◇ P) ⊢ |=[W]=>◇ P := by sorry

/-- [modw] over [bupdw_0] -/
theorem modw_bupdw0 [BI PROP] [BIUpdate PROP] {W W' P : PROP} :
  modw (bupdw0 W) W' P ⊣⊢ |=[iprop(W ∗ W')]=>◇ P := by sorry

end bupdw0

/- theorems on [fupdw] -/

namespace fupdw

/-- Modify the world satisfaction of [fupdw] -/
theorem fupdw_incl_fupd [BI PROP] [BIFUpdate PROP] {W W' P : PROP} {E E' : CoPset} :
  ⊢ (W ={E}=∗ W' ∗ (W' ={E'}=∗ W)) -∗ (|=[W']{E,E'}=> P) =[W]{E,E'}=∗ P := by
  sorry

theorem fupdw_incl [BI PROP] [BIFUpdate PROP] [WsatIncl W W' Wr] {E E'} {P : PROP} :
  (|=[W']{E,E'}=> P) ⊢ |=[W]{E,E'}=> P := by sorry

/-- Expand the world satisfaction of a view shift, for presentation -/
theorem vsw_expand [BI PROP] [BIFUpdate PROP] {W W' P Q : PROP} {E E'} :
  ⊢ □ (P =[W]{E,E'}=∗ Q) -∗ □ (P =[iprop(W ∗ W')]{E,E'}=∗ Q) := by
  iintro Hp; istop
  apply intuitionistically_mono
  iintro f P; ispecialize f P; istop
  apply entails_trans.trans (emp_sep.1)
  simp [fupdw, modw]
  iintro f ⟨ W, W' ⟩; ispecialize f W; istop
  apply entails_trans.trans (sep_comm.1)
  apply entails_trans.trans (BIFUpdate.frame_r _ _)
  apply BIFUpdate.mono
  iintro ⟨ ⟨ W, Q ⟩, W' ⟩; isplit r [Q]
  · isplit l [W] <;> iassumption
  · iassumption

/-- Introduce [fupdw] -/
theorem fupdw_mask_intro [BI PROP] [BIFUpdate PROP] {E E'} {W P : PROP} : E' ⊆ E →
  ((|={E',E}=> emp) -∗ P) ⊢ |=[W]{E,E'}=> P := by
  intro HE
  simp [fupdw, modw]
  iintro f W; istop
  apply entails_trans.trans _ (BIFUpdate.mono _ _ _ _ sep_comm.1)
  apply entails_trans.trans _ (BIFUpdate.frame_r _ _)
  iintro ⟨ f, W ⟩; isplit l [f]
  · apply (fupd_mask_intro _ _ _ HE)
  · iassumption

theorem idw_fupdw [BI PROP] [BIFUpdate PROP] E {W P : PROP} :
  (|->[W] P) ⊢ |=[W]{E}=> P := by
  simp [idw, fupdw, modw]; apply wand_mono_r
  apply fupd_intro

theorem idw0_fupdw [BI PROP] [BIFUpdate PROP] E {W P : PROP} :
  (|->[W]◇ P) ⊢ |=[W]{E}=> P := by
  simp [idw0, fupdw, modw]; apply wand_mono_r
  apply entails_trans.trans _ (BIFUpdate.except0 _)
  unfold BIBase.except0
  iintro HWP; icases HWP with ⟨ HF | ⟨ W, P ⟩ ⟩
  · ileft; iassumption
  · iright; istop; apply fupd_intro

theorem bupdw_fupdw [BI PROP] [BIUpdate PROP] [BIFUpdate PROP] [BIUpdateFUpdate PROP] E {W P : PROP} :
  (|=[W]=> P) ⊢ |=[W]{E}=> P := by
  simp [bupdw, fupdw, modw]; apply wand_mono_r
  apply BIUpdateFUpdate.fupd_of_bupd

theorem bupdw_0_fupdw [BI PROP] [BIUpdate PROP] [BIFUpdate PROP] [BIUpdateFUpdate PROP] E {W P : PROP} :
  (|=[W]=>◇ P) ⊢ |=[W]{E}=> P := by
  simp [bupdw0, fupdw, modw, bupd0, relax0]; apply wand_mono_r
  apply entails_trans.trans _ (fupd_except0 _ _ _)
  apply BIUpdateFUpdate.fupd_of_bupd

end fupdw
