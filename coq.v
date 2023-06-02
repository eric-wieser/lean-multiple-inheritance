From Coq Require Import Unicode.Utf8.

Module Flat.
  Module add_monoid.
  Class add_monoid A : Type := { zero : A; add : A → A → A; }.
  End add_monoid.

  Module add_comm_monoid.
  Class add_comm_monoid A : Type :=
  { zero : A; add : A → A → A }.
  #[global] Instance to_add_monoid {A : Type} `{add_comm_monoid A} : add_monoid.add_monoid A :=
  { zero := zero; add := add }.
  End add_comm_monoid.

  Module semiring.
  Class semiring A : Type :=
  { zero : A; add : A → A → A; one : A; mul : A → A → A; }.
  #[global] Instance to_add_monoid {A : Type} `{semiring A} : add_comm_monoid.add_comm_monoid A :=
  { zero := zero; add := add }.
  End semiring.


  Module add_group.
  Class add_group A : Type := { zero : A; add : A → A → A; neg : A → A }.
  #[global] Instance to_add_monoid {A : Type} `{add_group A} : add_monoid.add_monoid A :=
  { zero := zero; add := add }.
  End add_group.

  Module add_comm_group.
  Class add_comm_group A : Type :=
  { zero : A; add : A → A → A; neg : A → A }.
  #[global] Instance to_add_comm_monoid {A : Type} `{add_comm_group A} : add_comm_monoid.add_comm_monoid A :=
  { zero := zero; add := add }.
  #[global] Instance to_add_group {A : Type} `{add_comm_group A} : add_group.add_group A :=
  { zero := zero; add := add; neg := neg }.
  End add_comm_group.

  Module ring.
  Class ring A : Type :=
  { zero : A; add : A → A → A; one : A; mul : A → A → A; neg : A → A }.
  #[global] Instance to_semiring {A : Type} `{ring A} : semiring.semiring A :=
  { zero := zero; add := add; one := one; mul := mul }.
  #[global] Instance to_add_comm_group {A : Type} `{ring A} : add_comm_group.add_comm_group A :=
  { zero := zero; add := add; neg := neg }.
  End ring.

  Class module (A B : Type) `{semiring.semiring A} `{add_comm_monoid.add_comm_monoid B} :=
  { smul : A → B → B }.
  #[global] Instance semiring_to_module (A : Type) `{semiring.semiring A} : module A A := { smul := semiring.mul }.

  Theorem neg_smul {R M : Type} {HR : ring.ring R} {HM : add_comm_group.add_comm_group M} {HRM : module R M}
    (r : R) (m : M) :
    smul (add_group.neg r) m = add_group.neg (smul r m).
  Proof.
  Admitted.

  Definition test_1 (R : Type) `{ring.ring R} : module R R := _.

  Definition test_2 {R : Type} `{ring.ring R} (r : R) (r' : R) :
    smul (add_group.neg r) r' = add_group.neg (smul r r') := neg_smul r r'.

End Flat.

Module Nested.
  (* Uncomment this line to make the failure below succeed *)
  (* Set Primitive Projections. *)

  Module add_monoid.
  Class add_monoid A : Type := { zero : A; add : A → A → A; }.
  End add_monoid.
  
  Module add_comm_monoid.
  Class add_comm_monoid A : Type := {to_add_monoid : add_monoid.add_monoid A}.
  #[global] Existing Instance to_add_monoid | 1.
  End add_comm_monoid.

  Module semiring.
  Class semiring A : Type :=
  { to_add_comm_monoid : add_comm_monoid.add_comm_monoid A; one : A; mul : A → A → A }.
  #[global] Existing Instance to_add_comm_monoid | 1.
  End semiring.

  Module add_group.
  Class add_group A : Type := { to_add_monoid : add_monoid.add_monoid A; neg : A → A }.
  #[global] Existing Instance to_add_monoid | 1.
  End add_group.

  
  Module add_comm_group.
  Class add_comm_group A : Type := { to_add_group : add_group.add_group A }.
  #[global] Existing Instance to_add_group | 1.
  #[global] Instance to_add_comm_monoid
    {A : Type} `{add_comm_group A} : add_comm_monoid.add_comm_monoid A | 10 :=
  { to_add_monoid := add_group.to_add_monoid }.
  End add_comm_group.

  Module ring.
  Class ring A : Type := { to_semiring : semiring.semiring A; neg : A → A }.
  #[global] Existing Instance ring.to_semiring | 1.
  (* @[priority 100] *)
  #[global] Instance to_add_comm_group
    {A : Type} `{ring A} : add_comm_group.add_comm_group A | 10 :=
  { to_add_group := {| add_group.neg := neg |} }.
  End ring.

  Set Printing Implicit.

  Class module (A B : Type) `{semiring.semiring A} `{add_comm_monoid.add_comm_monoid B} :=
  { smul : A → B → B }.
  #[global] Instance semiring_to_module (A : Type) `{semiring.semiring A} : module A A := { smul := semiring.mul }.

  Theorem neg_smul {R M : Type}
    {HR : ring.ring R} {HM : add_comm_group.add_comm_group M} {HRM : module R M}
    (r : R) (m : M) :
    smul (add_group.neg r) m = add_group.neg (smul r m).
  Proof.
  Admitted.

  Definition test_1 (R : Type) `{ring.ring R} : module R R := _.

  Definition test_2 {R : Type} `{ring.ring R} (r : R) (r' : R) :
    smul (add_group.neg r) r' = add_group.neg (smul r r') := neg_smul r r'.
    (* fails without `Primitive Projections` *)

End Nested.
