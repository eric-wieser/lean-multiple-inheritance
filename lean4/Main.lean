
namespace nested

  class add_monoid (α : Type) :=
  (zero : α) (add : α → α → α)

  class add_comm_monoid (α : Type) extends add_monoid α

  class semiring (α : Type) extends add_comm_monoid α :=
  (one : α) (mul : α → α → α)

  attribute [instance 1000] semiring.toadd_comm_monoid

  class add_group (α : Type) extends add_monoid α :=
  (neg : α → α)

  class add_comm_group (α : Type) extends add_group α, add_comm_monoid α

  attribute [instance 10] add_comm_group.toadd_comm_monoid

  #check add_comm_group.toadd_comm_monoid

  class ring (α : Type) extends semiring α, add_comm_group α 

  attribute [instance 0] ring.toadd_comm_group

end nested

namespace nested

  class module (α β : Type) [semiring α] [add_comm_monoid β] :=
  (smul : α → β → β)

  instance semiring.to_module (α) [semiring α] : module α α := { smul := semiring.mul }

  -- fails! This works in Lean 3 presumably because we got lucky with instance priorities
  example (R) [iR : ring R] : module R R := by infer_instance

  -- ok
  set_option synthInstance.etaExperiment true in
  example (R) [iR : ring R] : module R R := by infer_instance

  theorem neg_smul {R M} [ring R] [add_comm_group M] [module R M] (r : R) (m : M) :
    module.smul (add_group.neg r) m = add_group.neg (module.smul r m) := sorry

  -- fails
  example {R} [iR : ring R] (r : R) (r' : R) :
    module.smul (add_group.neg r) r' = add_group.neg (module.smul r r') := neg_smul r r'

  -- ok
  set_option synthInstance.etaExperiment true in
  example {R} [iR : ring R] (r : R) (r' : R) :
    module.smul (add_group.neg r) r' = add_group.neg (module.smul r r') := neg_smul r r'

end nested
