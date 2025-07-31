import Iris.BI
import Iris.Algebra.Own
import Iris.Std.Namespaces

inductive cif_binsel where
| /- Conjunction -/ cifs_and
| /- Disjunction -/ cifs_or
| /- Implication -/ cifs_imp
| /- Separating conjunction -/ cifs_sep
| /- Magic wand -/ cifs_wand

inductive cif_unsel where
| /- Plainly -/ cifs_plain
| /- Persistently -/ cifs_pers
| /- Basic update -/ cifs_bupd
| /- Except-0 -/ cifs_except0

inductive cif.{u} (FF : Iris.GFunctors) : Type (u + 1) where
| /- Universal quantifier -/ cifs_all {A : Type u} (Φ : A -> cif FF)
| /- Existential quantifier -/ cifs_ex {A : Type u} (Φ : A -> cif FF)
| /- Binary operator -/ cifs_bin (s : cif_binsel) (P : cif FF) (Q : cif FF)
| /- Unary operator -/ cifs_un (s : cif_unsel) (P : cif FF)
| /- Pure proposition -/ cifs_pure (P : Prop)
| /- Later -/ cifs_later (iP : Iris.IProp FF)
| /- Invariant -/ cifs_inv (N : Namespace) (fml : cif FF)
| /- Custom selector -/ cifs_own [Iris.CMRA A] [inG FF A] (a : A)

def cifs_wandiff {FF} (P Q : cif FF) : cif FF :=
  cif.cifs_bin cif_binsel.cifs_and
    (cif.cifs_bin cif_binsel.cifs_wand P Q)
    (cif.cifs_bin cif_binsel.cifs_wand Q P)

namespace cif

def cifs_plain (P : cif FF) : cif FF := cif.cifs_un cif_unsel.cifs_plain P
def cifs_pers (P : cif FF) : cif FF := cif.cifs_un cif_unsel.cifs_pers P
def cifs_bupd (P : cif FF) : cif FF := cif.cifs_un cif_unsel.cifs_bupd P
def cifs_except0 (P : cif FF) : cif FF := cif.cifs_un cif_unsel.cifs_except0 P

def cifs_and (P Q : cif FF) : cif FF := cif.cifs_bin cif_binsel.cifs_and P Q
def cifs_or (P Q : cif FF) : cif FF := cif.cifs_bin cif_binsel.cifs_or P Q
def cifs_imp (P Q : cif FF) : cif FF := cif.cifs_bin cif_binsel.cifs_imp P Q
def cifs_sep (P Q : cif FF) : cif FF := cif.cifs_bin cif_binsel.cifs_sep P Q
def cifs_wand (P Q : cif FF) : cif FF := cif.cifs_bin cif_binsel.cifs_wand P Q

end cif
