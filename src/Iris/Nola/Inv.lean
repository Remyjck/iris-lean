import Iris.BI
import Iris.BI.Updates
import Iris.Algebra.CMRA
import Iris.Algebra.OFE
import Iris.Algebra.UPred
import Iris.Algebra.IProp
import Iris.Instances.UPred.Instance
import Iris.Algebra.Own
import Iris.Std.Namespaces

import Iris.Nola.Syntax

section sinv

axiom sinv_tok (i : Pos) (F : Fml FF) : Iris.IProp FF

axiom sinv_tok_lift (i : Pos) (F : Fml FF) :
  sinv_tok i (liftFml F) ⊣⊢ sinv_tok i F

axiom sinv_auth_tok (M : List (Fml FF)) : Iris.IProp FF

def sinv_wsat (sm : Fml FF -> Iris.IProp FF) : Iris.IProp FF :=
  iprop(∃ M, sinv_auth_tok M ∗ [∗] (List.map (fun F => (sm F)) M))

axiom sinv_wsat_timeless (sm : Fml FF -> Iris.IProp FF) :
  Iris.BI.Timeless (sinv_wsat sm)

axiom sinv_auth_tok_alloc (M : List (Fml FF)) F :
  ⊢ sinv_auth_tok M ==∗ sinv_auth_tok (F :: M) ∗ sinv_tok (Pos.ofNat (List.length M)) F

axiom sinv_tok_acc {i : Pos} {sm : Fml FF -> Iris.IProp FF} {F : Fml FF} :
  ⊢ sinv_tok i F -∗
    sinv_wsat sm -∗
    sm F ∗ (sm F -∗ sinv_wsat sm)

end sinv

section inv

def inv_tok (N : Namespace) (F : Fml FF) : Iris.IProp FF :=
  iprop(∃ i, ⌜i ∈ N⌝ ∗ sinv_tok i F)

def magic_inv {sm : Fml FF -> Iris.IProp FF} N F :=
  iprop(∃ Q, (sm Q ∗-∗ sm F) ∗ inv_tok N F)

theorem inv_tok_subset {N N'} {F : Fml FF} :
  N ⊆ N' ->
  inv_tok N F ⊢ inv_tok N' F := by
  intros Hsubseteq
  unfold inv_tok
  iintro ⟨ i, %Hin, Hi ⟩
  iexists i; isplit; ipure_intro; apply (Hsubseteq Hin)
  iexact Hi

axiom inv_tok_alloc {sm : Fml FF -> Iris.IProp FF} (F : Fml FF) N :
  ⊢ sm F ==∗ inv_tok N F

end inv
