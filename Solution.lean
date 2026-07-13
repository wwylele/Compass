module

public import Compass

public section

namespace EuclideanGeometry

variable {V P : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [hrank : Fact (Module.finrank ℝ V = 2)]
  [MetricSpace P] [NormedAddTorsor V P]

theorem _root_.Challenge.not_exist_angle_trisection :
    ∃ p₁ p₂ p₃ : P, p₁ ≠ p₂ ∧ p₂ ≠ p₃ ∧ p₁ ≠ p₃ ∧
    ¬ ∃ q₁ q₂ q₃ : P,
    ConstructiblePoint {p₁, p₂, p₃} q₁ ∧
    ConstructiblePoint {p₁, p₂, p₃} q₂ ∧
    ConstructiblePoint {p₁, p₂, p₃} q₃ ∧
    3 * ∠ q₁ q₂ q₃ = ∠ p₁ p₂ p₃ :=
  EuclideanGeometry.not_exist_angle_trisection

end EuclideanGeometry
