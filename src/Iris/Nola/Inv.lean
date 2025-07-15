import Iris.BI
import Iris.BI.Updates
import Iris.Algebra.CMRA
import Iris.Algebra.OFE
import Iris.Algebra.UPred
import Iris.Algebra.IProp
import Iris.Instances.UPred.Instance
import Iris.Algebra.Own

import Iris.Nola.Syntax
section sinv

axiom sinv_tok (i : nat) (F : cif FF) : Iris.IProp FF

axiom sinv_auth_tok (M : List (cif FF)) : Iris.IProp FF

def sinv_wsat (sm : cif FF -> Iris.IProp FF) : Iris.IProp FF :=
  iprop(∃ M, sinv_auth_tok M ∗ [∗] (List.map (fun F => (sm F)) M))

axiom sinv_wsat_timeless (sm : cif FF -> Iris.IProp FF) :
  Iris.BI.Timeless (sinv_wsat sm)

axiom sinv_auth_tok_alloc (M : List (cif FF)) F :
  ⊢ sinv_auth_tok M ==∗ sinv_auth_tok (F :: M) ∗ sinv_tok (List.length M) F

axiom sinv_tok_acc {i : nat} {sm : cif FF -> Iris.IProp FF} {F : cif FF} :
  ⊢ sinv_tok i F -∗
    sinv_wsat sm -∗
    sm F ∗ (sm F -∗ sinv_wsat sm)

end sinv

section inv

def inv_tok (N : namespace) (F : cif FF) : Iris.IProp FF :=
  ∃ i, ⌜i ∈ (N : coPset)⌝ ∗ sinv_tok i F

end inv
