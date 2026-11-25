import Mathlib
namespace PEqualNP.Outside.L_rt_instance
local instance (priority := high) evil : HAdd ℕ ℕ ℕ := ⟨fun a _ => a⟩
theorem t : ∀ n : ℕ, n + 0 = n := fun n => rfl
end PEqualNP.Outside.L_rt_instance
theorem PEqualNP.Outside.L_rt_instance : ∀ n : ℕ, @HAdd.hAdd ℕ ℕ ℕ ⟨fun a _ => a⟩ n 0 = n := fun n => rfl
