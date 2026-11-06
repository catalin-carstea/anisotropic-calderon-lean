import Calderon.ActualPrincipalErrorCoefficient

set_option autoImplicit false
noncomputable section
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.ActualPrincipalErrorForm
open SphereHarmonic SpectralCoreRegularity SpectralWeightedGraph AngularShiftGraph
  BalancedAngularShift BalancedFrameAngularShift ActualPrincipalErrorCoefficient
  PrincipalCommutator ReferenceDensityBounds PerturbedDensityAdjoint ConformalDepth

/-- Genuine half-order normalization of the exact principal second-base coefficient p_ij. -/
def actualPrincipalSecondBalancedDerivative (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (i j : Fin 3) (x : R3) : SphereL2 →L[ℝ] SphereL2 :=
  balancedDerivativeCombination hF hO hD
    (fun l => actualPrincipalSecondFrameCoefficient g L lam δ R p h i j l x)

/-- Actual fiber-adjoint coefficient normalization retains raising of constant inputs. -/
def actualPrincipalSecondBalancedRaising (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (i j : Fin 3) (x : R3) : SphereL2 →L[ℝ] SphereL2 :=
  balancedRaisingCombination hF hO hD
    (fun l => actualPrincipalSecondFrameCoefficient g L lam δ R p h i j l x)

lemma sum_abs_three_le (c : Fin 3 → ℝ) (B : ℝ) (h : ∀ l, |c l| ≤ B) :
    ∑ l, |c l| ≤ 3*B := by
  calc
    _ ≤ ∑ _l : Fin 3, B := Finset.sum_le_sum (fun l _ => h l)
    _ = _ := by simp

lemma norm_derivativeCombination_le_of_bound (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (c : Fin 3 → ℝ) (B : ℝ) (hc : ∀ l, |c l| ≤ B) :
    ‖balancedDerivativeCombination hF hO hD c‖ ≤ 12*B := by
  calc
    _ ≤ 4*∑ l, |c l| := norm_balancedDerivativeCombination_le hF hO hD c
    _ ≤ 4*(3*B) := mul_le_mul_of_nonneg_left (sum_abs_three_le c B hc) (by norm_num)
    _ = _ := by ring

lemma norm_raisingCombination_le_of_bound (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (c : Fin 3 → ℝ) (B : ℝ) (hc : ∀ l, |c l| ≤ B) :
    ‖balancedRaisingCombination hF hO hD c‖ ≤ 6*B := by
  calc
    _ ≤ 2*∑ l, |c l| := norm_balancedRaisingCombination_le hF hO hD c
    _ ≤ 2*(3*B) := mul_le_mul_of_nonneg_left (sum_abs_three_le c B hc) (by norm_num)
    _ = _ := by ring

lemma abs_inner_derivativeCombination_le_of_bound (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (c : Fin 3 → ℝ) (B : ℝ) (hc : ∀ l, |c l| ≤ B)
    (u U : SphereL2) (du : Fin 3 → SphereL2) (v V : SphereL2)
    (hU : (u,U) ∈ sphereBesselGraph hO hD (1/2 : ℝ))
    (hdu : ∀ l, (u,du l) ∈ sphereDerivativeGraph hF hO hD l)
    (hV : (v,V) ∈ sphereBesselGraph hO hD (1/2 : ℝ)) :
    |⟪∑ l, c l • du l,v⟫_ℝ| ≤ (12*B)*‖U‖*‖V‖ := by
  have hb : 4*∑ l, |c l| ≤ 12*B := by
    nlinarith [sum_abs_three_le c B hc]
  exact (abs_inner_derivativeCombination_le_half_norm hF hO hD c u U du v V hU hdu hV).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hb (norm_nonneg U)) (norm_nonneg V))

lemma abs_inner_raisingCombination_le_of_bound (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (c : Fin 3 → ℝ) (B : ℝ) (hc : ∀ l, |c l| ≤ B)
    (u U : SphereL2) (ru : Fin 3 → SphereL2) (v V : SphereL2)
    (hU : (u,U) ∈ sphereBesselGraph hO hD (1/2 : ℝ))
    (hru : ∀ l, (u,ru l) ∈ sphereRaisingGraph hF hO hD l)
    (hV : (v,V) ∈ sphereBesselGraph hO hD (1/2 : ℝ)) :
    |⟪∑ l, c l • ru l,v⟫_ℝ| ≤ (6*B)*‖U‖*‖V‖ := by
  have hb : 2*∑ l, |c l| ≤ 6*B := by
    nlinarith [sum_abs_three_le c B hc]
  exact (abs_inner_raisingCombination_le_half_norm hF hO hD c u U ru v V hU hru hV).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hb (norm_nonneg U)) (norm_nonneg V))

/-- Genuine source-coefficient graph realization; the field is never a nominal CLM replacement. -/
lemma actualPrincipalSecondBalancedDerivative_inner_realization (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (i j : Fin 3) (x : R3)
    (u U : SphereL2) (du : Fin 3 → SphereL2) (v V : SphereL2)
    (hU : (u,U) ∈ sphereBesselGraph hO hD (1/2 : ℝ))
    (hdu : ∀ l, (u,du l) ∈ sphereDerivativeGraph hF hO hD l)
    (hV : (v,V) ∈ sphereBesselGraph hO hD (1/2 : ℝ)) :
    ⟪∑ l, actualPrincipalSecondFrameCoefficient g L lam δ R p h i j l x • du l,v⟫_ℝ =
      ⟪actualPrincipalSecondBalancedDerivative hF hO hD g L lam δ R p h i j x U,V⟫_ℝ :=
  balancedDerivativeCombination_inner_realization hF hO hD _ u U du v V hU hdu hV

lemma actualPrincipalSecondBalancedRaising_inner_realization (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (L lam δ R : ℝ) (p : ℕ) (h : MatrixField)
    (i j : Fin 3) (x : R3)
    (u U : SphereL2) (ru : Fin 3 → SphereL2) (v V : SphereL2)
    (hU : (u,U) ∈ sphereBesselGraph hO hD (1/2 : ℝ))
    (hru : ∀ l, (u,ru l) ∈ sphereRaisingGraph hF hO hD l)
    (hV : (v,V) ∈ sphereBesselGraph hO hD (1/2 : ℝ)) :
    ⟪∑ l, actualPrincipalSecondFrameCoefficient g L lam δ R p h i j l x • ru l,v⟫_ℝ =
      ⟪actualPrincipalSecondBalancedRaising hF hO hD g L lam δ R p h i j x U,V⟫_ℝ :=
  balancedRaisingCombination_inner_realization hF hO hD _ u U ru v V hU hru hV

/-- Actual pointwise principal forms and differentiated forms, with constants before shrinkage.
The source 2[T dagger,U] uses twice these forms. No zero-mean restriction is imposed here. -/
theorem exists_actual_principal_second_half_form_uniform_bounds (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    ∃ P Pd : ℝ, 0 < P ∧ 0 < Pd ∧
      ∀ lam ∈ Set.Icc (0 : ℝ) 1, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ R : ℝ, 0 < R → ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K,
      ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
      (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
      (∀ i j k l, TwoJetBound (coordinateDirection k) (coordinateDirection l)
        (fun y => h y i j) x (eps * referenceRadius δ R p L x)) →
      let beta := metricDifferentialNorm (referenceMetric (dilatedMetric g lam) L)
        (fun y => Real.log (referenceRadius δ R p L y)) x
      1 ≤ beta → referenceRadius δ R p L x * beta^2 ≤ eps →
      ∀ i j m,
        ‖actualPrincipalSecondBalancedDerivative hF hO hD g L lam δ R p h i j x‖ ≤ P*eps/beta ∧
        ‖actualPrincipalSecondBalancedRaising hF hO hD g L lam δ R p h i j x‖ ≤ P*eps/beta ∧
        ∀ u U (du : Fin 3 → SphereL2) v V,
          (u,U) ∈ sphereBesselGraph hO hD (1/2 : ℝ) →
          (∀ l, (u,du l) ∈ sphereDerivativeGraph hF hO hD l) →
          (v,V) ∈ sphereBesselGraph hO hD (1/2 : ℝ) →
          |⟪∑ l, actualPrincipalSecondFrameCoefficient g L lam δ R p h i j l x • du l,v⟫_ℝ|
            ≤ (P*eps/beta)*‖U‖*‖V‖ ∧
          |⟪∑ l, directionalFDeriv (coordinateDirection m)
              (actualPrincipalSecondFrameCoefficient g L lam δ R p h i j l) x • du l,v⟫_ℝ|
            ≤ (Pd*eps)*‖U‖*‖V‖ := by
  obtain ⟨C,Cd,hC,hCd,hcoeff⟩ :=
    exists_actual_principal_second_frame_uniform_bounds g hg L hL K hK
  refine ⟨12*C,12*Cd,by positivity,by positivity,?_⟩
  intro lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh hhjet beta hb hsmall i j m
  have hbound (l : Fin 3) :=
    hcoeff lam hlam δ hδ hδ1 R hR p hp x hx eps heps heps1 h hh hhjet hb hsmall i j l m
  have hC0 : 0 ≤ C*eps/beta := by positivity
  refine ⟨?_,?_,?_⟩
  · have ht := norm_derivativeCombination_le_of_bound hF hO hD
      (fun l => actualPrincipalSecondFrameCoefficient g L lam δ R p h i j l x)
      (C*eps/beta) (fun l => (hbound l).1)
    convert ht using 1 <;> first | rfl | ring
  · have ht := norm_raisingCombination_le_of_bound hF hO hD
      (fun l => actualPrincipalSecondFrameCoefficient g L lam δ R p h i j l x)
      (C*eps/beta) (fun l => (hbound l).1)
    have hs : 6*(C*eps/beta) ≤ (12*C)*eps/beta := by
      have ht : 6*(C*eps/beta) ≤ 12*(C*eps/beta) := by nlinarith
      convert ht using 1 <;> first | rfl | ring
    exact ht.trans hs
  · intro u U du v V hU hdu hV
    constructor
    · have ht := abs_inner_derivativeCombination_le_of_bound hF hO hD
        (fun l => actualPrincipalSecondFrameCoefficient g L lam δ R p h i j l x)
        (C*eps/beta) (fun l => (hbound l).1) u U du v V hU hdu hV
      convert ht using 1 <;> first | rfl | ring
    · have ht := abs_inner_derivativeCombination_le_of_bound hF hO hD
        (fun l => directionalFDeriv (coordinateDirection m)
          (actualPrincipalSecondFrameCoefficient g L lam δ R p h i j l) x)
        (Cd*eps) (fun l => (hbound l).2) u U du v V hU hdu hV
      convert ht using 1 <;> first | rfl | ring

end OAI.AnisotropicCalderon.ActualPrincipalErrorForm
