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

inductive cif (FF : Iris.GFunctors) : Type (u + 1) where
| /- Universal quantifier -/ cifs_all (A : Type u) (Φ : A -> cif FF)
| /- Existential quantifier -/ cifs_ex (A : Type u) (Φ : A -> cif FF)
| /- Binary operator -/ cifs_bin (s : cif_binsel) (P Q : cif FF)
| /- Unary operator -/ cifs_un (s : cif_unsel) (P : cif FF)
| /- Pure proposition -/ cifs_pure (P : Prop)
| /- Later -/ cifs_later (iP : Iris.IProp FF)
| /- Invariant -/ cifs_inv (N : Namespace) (fml : cif FF)
| /- Custom selector -/ cifs_own [Iris.CMRA A] [inG FF A] (a : A)
