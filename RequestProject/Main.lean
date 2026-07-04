import RequestProject.Reduction
import RequestProject.Upper
import RequestProject.Lower
import RequestProject.LowerFinal

open scoped BigOperators
open Filter Topology

namespace Erdos1005

/-- **Erdős problem 1005.** With `f(n)` the minimum number of Farey fractions strictly
between two badly ordered Farey fractions of order `n`, we have `f(n) = (1/4 + o(1)) n`,
i.e. `f(n)/n → 1/4`. -/
theorem erdos_1005 :
    Tendsto (fun n : ℕ => (fVal n : ℝ) / n) atTop (nhds (1 / 4)) :=
  erdos_1005_of_bounds fVal_upper_bound fVal_lower_bound

end Erdos1005
