import Calderon.ActualFiniteHarmonicModelSourceEnergy

set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
open SphereHarmonic ActualFiniteHarmonicCore SpectralWeightedGraph BalancedAngularShift
  SectionFiveErrorForms ReferenceDensityBounds
variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
private abbrev nativeAngularEnergyFunction :
    CoeFun (smoothCompactFiniteSphereCore hO hD) (fun _ => R3 → SphereL2) :=
  ⟨fun F => F.val⟩
attribute [local instance] nativeAngularEnergyFunction

lemma abs_inner_coreDerivative_le_half
    (hF : SphereFischerInner) (a : Fin 3)
    (U V : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    |⟪coreDerivative hO hD hF a U x,V x⟫_ℝ| ≤
      4 * ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x‖ *
        ‖coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) V x‖ := by
  exact abs_inner_derivative_le_half_norm hF hO hD a (U x)
    (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) U x)
    (coreDerivative hO hD hF a U x) (V x)
    (coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) V x)
    (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) U x)
    (coreDerivative_graph hO hD hF a U x)
    (coreWeightOperator_graph hO hD (besselWeight (1/2 : ℝ)) V x)

theorem angular_second_scalar_remainders_le_sourceEnergy
    (hF : SphereFischerInner) (a i j : Fin 3)
    (beta m C eps s t : ℝ) (hb : 0 < beta) (hm : 0 ≤ m) (hC : 0 ≤ C) (heps : 0 ≤ eps)
    (hs : |s| ≤ m*(C*eps)) (ht : |t| ≤ m*(C*eps/beta))
    (F : smoothCompactFiniteSphereCore hO hD) (x : R3) :
    |s * ⟪F x,coreDerivative hO hD hF a
        (coreDirectionalDerivative hO hD (coordinateDirection j) F) x⟫_ℝ| +
      |t * ⟪coreDirectionalDerivative hO hD (coordinateDirection i) F x,
        coreDerivative hO hD hF a (coreDirectionalDerivative hO hD (coordinateDirection j) F) x⟫_ℝ| ≤
      m*(8*C*eps)*finiteCoreSourceEnergy hO hD beta F x := by
  let U := coreDirectionalDerivative hO hD (coordinateDirection j) F
  let V := coreDirectionalDerivative hO hD (coordinateDirection i) F
  let H (G : smoothCompactFiniteSphereCore hO hD) :=
    coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) G x
  let N := finiteCoreSourceEnergy hO hD beta F x
  have hp0 : |⟪F x,coreDerivative hO hD hF a U x⟫_ℝ| ≤ 4*‖H U‖*‖H F‖ := by
    rw [real_inner_comm]
    exact abs_inner_coreDerivative_le_half hO hD hF a U F x
  have hp1 : |⟪V x,coreDerivative hO hD hF a U x⟫_ℝ| ≤ 4*‖H U‖*‖H V‖ := by
    rw [real_inner_comm]
    exact abs_inner_coreDerivative_le_half hO hD hF a U V x
  have hprod0 : ‖H F‖*‖H U‖ ≤ N :=
    norm_half_mul_gradient_half_le_finiteCoreSourceEnergy hO hD beta hb F x j
  have hprod1 : beta⁻¹*(‖H V‖*‖H U‖) ≤ N :=
    inv_beta_mul_gradient_norms_le_finiteCoreSourceEnergy hO hD beta hb.le F x i j
  have h0 : |s * ⟪F x,coreDerivative hO hD hF a U x⟫_ℝ| ≤ m*(4*C*eps)*N := by
    rw [abs_mul]
    calc
      _ ≤ (m*(C*eps))*(4*‖H U‖*‖H F‖) := mul_le_mul hs hp0 (abs_nonneg _) (by positivity)
      _ = (m*(4*C*eps))*(‖H F‖*‖H U‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod0 (by positivity)
  have h1 : |t * ⟪V x,coreDerivative hO hD hF a U x⟫_ℝ| ≤ m*(4*C*eps)*N := by
    rw [abs_mul]
    calc
      _ ≤ (m*(C*eps/beta))*(4*‖H U‖*‖H V‖) := mul_le_mul ht hp1 (abs_nonneg _) (by positivity)
      _ = (m*(4*C*eps))*(beta⁻¹*(‖H V‖*‖H U‖)) := by simp only [div_eq_mul_inv]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hprod1 (by positivity)
  calc
    _ ≤ m*(4*C*eps)*N + m*(4*C*eps)*N := add_le_add h0 h1
    _ = _ := by ring

end OAI.AnisotropicCalderon.ActualFiniteHarmonicModel
