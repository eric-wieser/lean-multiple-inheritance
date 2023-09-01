import tactic.show_term

/-! ### Native spelling of flat structures -/

namespace idealized
  -- not legal in Lean 3 without this line
  set_option old_structure_cmd true

  class add_monoid (α : Type) :=
  (zero : α) (add : α → α → α)

  class add_comm_monoid (α : Type) extends add_monoid α

  class semiring (α : Type) extends add_comm_monoid α :=
  (one : α) (mul : α → α → α)

  class add_group (α : Type) extends add_monoid α :=
  (neg : α → α)

  class add_comm_group (α : Type) extends add_group α, add_comm_monoid α

  class ring (α : Type) extends semiring α, add_comm_group α 

end idealized

/-! ### Setup for flat / nested versions -/

namespace flat
  class add_monoid (α : Type) :=
  (zero : α) (add : α → α → α)

  class add_comm_monoid (α : Type) :=
  (zero : α) (add : α → α → α)
  instance add_comm_monoid.to_add_monoid
    (α : Type) [i : add_comm_monoid α] : add_monoid α := { ..i }

  class semiring (α : Type) :=
  (zero : α) (add : α → α → α)
  (one : α) (mul : α → α → α)
  instance semiring.to_add_comm_monoid
    (α : Type) [i : semiring α] : add_comm_monoid α := { ..i }

  class add_group (α : Type) :=
  (zero : α) (add : α → α → α)
  (neg : α → α)
  instance add_group.to_add_monoid
    (α : Type) [i : add_group α] : add_monoid α := { ..i }

  class add_comm_group (α : Type) :=
  (zero : α) (add : α → α → α) (neg : α → α)
  instance add_comm_group.to_add_group
    (α : Type) [i : add_comm_group α] : add_group α := { ..i }
  instance add_comm_group.to_add_comm_monoid
    (α : Type) [i : add_comm_group α] : add_comm_monoid α := { ..i }


  class ring (α : Type) :=
  (zero one : α) (add mul : α → α → α) (neg : α → α)
  instance ring.to_semiring
    (α : Type) [i : ring α] : semiring α := { ..i }
  instance ring.to_add_comm_group
    (α : Type) [i : ring α] : add_comm_group α := { ..i }

end flat

namespace nested

  class add_monoid (α : Type) :=
  (zero : α) (add : α → α → α)
  
  class add_comm_monoid (α : Type) :=
  (to_add_monoid : add_monoid α)
  attribute [instance] add_comm_monoid.to_add_monoid

  
  class semiring (α : Type) :=
  (to_add_comm_monoid : add_comm_monoid α)
  (one : α) (mul : α → α → α)
  attribute [instance] semiring.to_add_comm_monoid


  class add_group (α : Type) :=
  (to_add_monoid : add_monoid α)
  (neg : α → α)
  attribute [instance] add_group.to_add_monoid

  
  class add_comm_group (α : Type) :=
  (to_add_group : add_group α)
  (neg : α → α)
  attribute [instance] add_comm_group.to_add_group
  @[priority 100] instance add_comm_group.to_add_comm_monoid
    {α : Type} [i : add_comm_group α] : add_comm_monoid α :=
  { to_add_monoid := i.to_add_group.to_add_monoid, ..i }

  class ring (α : Type) :=
  (to_semiring : semiring α)
  (neg : α → α)
  attribute [instance] ring.to_semiring
  @[priority 100] instance ring.to_add_comm_group
    (α : Type) [i : ring α] : add_comm_group α :=
  { to_add_group :=
    { to_add_monoid :=
        i.to_semiring.to_add_comm_monoid.to_add_monoid, ..i },
    .. i }

end nested

/-! ### Problems with `module` -/

namespace flat

  class module (α β : Type) [semiring α] [add_comm_monoid β] :=
  (smul : α → β → β)

  instance semiring.to_module (α) [semiring α] : module α α := { smul := semiring.mul }

  example (R) [iR : ring R] : module R R := by apply_instance

  lemma neg_smul {R M} [ring R] [add_comm_group M] [module R M] (r : R) (m : M) :
    module.smul (add_group.neg r) m = add_group.neg (module.smul r m) := sorry

  -- ok
  example {R} [iR : ring R] (r : R) (r' : R) :
    module.smul (add_group.neg r) r' = add_group.neg (module.smul r r') := neg_smul r r'

end flat

namespace nested


  class module (α β : Type) [semiring α] [add_comm_monoid β] :=
  (smul : α → β → β)
  
  instance semiring.to_module (α) [iS : semiring α] : module α α := { smul := semiring.mul }

  example (R) [iR : ring R] : module R R := by show_term {apply_instance}

  lemma neg_smul {R M} [ring R] [add_comm_group M] [module R M] (r : R) (m : M) :
    module.smul (add_group.neg r) m = add_group.neg (module.smul r m) := sorry

  -- fails
  example {R} [iR : ring R] (r : R) (r' : R) :
    module.smul (add_group.neg r) r' = add_group.neg (module.smul r r') := neg_smul r r'

end nested

/-! Unfortunately figure 4 in the paper is incorrect; this demonstrates that the highlighted square
commutes after all.

This is a counterexample to the claim in
https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Some.20observations.20on.20eta.20experiment/near/355336941
-/
namespace cube

  class nu_na_semiring (R : Type)
  class nu_na_ring (R : Type) := (to_nu_na_semiring : nu_na_semiring R)
  attribute [instance] nu_na_ring.to_nu_na_semiring
  class na_semiring (R : Type) := (to_nu_na_semiring : nu_na_semiring R)
  attribute [instance] na_semiring.to_nu_na_semiring
  class nu_semiring (R : Type) := (to_nu_na_semiring : nu_na_semiring R)
  attribute [instance] nu_semiring.to_nu_na_semiring

  class na_ring (R : Type) := (to_na_semiring : na_semiring R)
  attribute [instance] na_ring.to_na_semiring
  class nu_ring (R : Type) := (to_nu_semiring : nu_semiring R)
  attribute [instance] nu_ring.to_nu_semiring

  class semiring (R : Type) := (to_nu_semiring : nu_semiring R)
  attribute [instance] semiring.to_nu_semiring
  class ring (R : Type) := (to_semiring : semiring R)
  attribute [instance] ring.to_semiring

  instance na_ring.to_nu_na_ring {R : Type} [i : na_ring R] : nu_na_ring R :=
    { ..i.to_na_semiring}
  instance nu_ring.to_nu_na_ring {R : Type} [i : nu_ring R] : nu_na_ring R :=
    { ..i.to_nu_semiring}
  instance semiring.to_na_semiring {R : Type} [i : semiring R] : na_semiring R :=
    { ..i.to_nu_semiring}

  instance ring.to_nu_ring {R : Type} [i : ring R] : nu_ring R :=
    { to_nu_semiring := semiring.to_nu_semiring }

  instance ring.to_na_ring {R : Type} [i : ring R] : na_ring R :=
    { to_na_semiring := semiring.to_na_semiring }

  example {R} [ring R] :
    @semiring.to_na_semiring _ (@ring.to_semiring R _) = @na_ring.to_na_semiring _ ring.to_na_ring :=
  rfl -- commutes after all; whoops

  -- for completeness
  example {R} [ring R] :
    @semiring.to_nu_semiring _ (@ring.to_semiring R _) = @nu_ring.to_nu_semiring _ ring.to_nu_ring :=
  rfl
  example {R} [ring R] :
    @nu_ring.to_nu_na_ring _ (@ring.to_nu_ring R _) = @na_ring.to_nu_na_ring _ ring.to_na_ring :=
  rfl

  -- the other three squares commute trivially, so we omit them
end cube
