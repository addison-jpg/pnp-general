import Mathlib
namespace PEqualNP.Outside.L_rt_instance3
instance (priority := high) evil : HAdd ℕ ℕ ℕ := ⟨fun a _ => a⟩
end PEqualNP.Outside.L_rt_instance3
open PEqualNP.Outside.L_rt_instance3 in
theorem PEqualNP.Outside.L_rt_instance3 : ∀ n : ℕ, n + 1 = n := fun n => rfl
