import Calderon.RadiusTwoCanonicalRowSpanWordEvaluations
import Calderon.RadiusTwoRowSpanWordOperatorRemainder
import Calderon.NativeCoordinateExpansion
import Calderon.NativeCoordinateExpansionSmoothness
import Calderon.NativeCoordinateWordFamilySmoothness
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators Distributions
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily ActualReferenceDDHigherGeometryJets ReferenceDensityBounds

theorem exists_radiusTwo_smooth_rowSpan_word_evaluations
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (η : ℕ → 𝓓(radiusTwoOpens, ℝ)) (S : Set R3) (hS : MeasurableSet S)
    (hSupp : ∀ j : ℕ, tsupport (η j : R3 → ℝ) ⊆ S)
    (hOne : ∀ j : ℕ, ∀ z ∈ tsupport (η j : R3 → ℝ), η (j+1) z = 1)
    (P : Set R3) (hPB : P ⊆ (radiusTwoOpens : Set R3) \ S)
    (a₀ : ℝ) (ha₀ : 0 < a₀) (ha₀1 : a₀ < 1)
    (Z : Set R3) (hZ : IsOpen Z) (hConvex : Convex ℝ Z) (hZBall : Z ⊆ ball (0 : R3) (2*a₀))
    (hEtaOne : ∀ z ∈ Z, η 0 z = 1) :
    let ν : Measure R3 := ((volume : Measure R3).restrict radiusTwoOpens).restrict S
    let R : RadiusTwoL2 →L[ℝ] Lp ℝ 2 ν := MeasureTheory.LpToLpRestrictCLM R3 ℝ ℝ
      ((volume : Measure R3).restrict radiusTwoOpens) 2 S
    let F : P → Lp ℝ 2 ν := fun p => R (K ⟨p,(hPB p.property).1⟩)
    let Y : Submodule ℝ (Lp ℝ 2 ν) :=
      (Submodule.span ℝ (Set.range F)).topologicalClosure
    let liftRows : P → Y := fun p => ⟨F p,
      (Submodule.le_topologicalClosure _)
        (Submodule.subset_span (show F p ∈ Set.range F from ⟨p,rfl⟩))⟩
    let e : (P →₀ ℝ) →ₗ[ℝ] Y := Finsupp.linearCombination ℝ liftRows
    ∃ C : ℕ → ℝ, (∀ n : ℕ, 0 ≤ C n) ∧
      ∃ L : List (Fin 3) → R3 → Y →L[ℝ] ℝ,
        (∀ (w : List (Fin 3)) (z : R3), z ∈ Z →
          ‖L w z‖ ≤ C w.length ∧
          (∀ c : P →₀ ℝ, L w z (e c) = Finsupp.linearCombination ℝ
            (fun p : P => coordinateFieldWordPartial w (G ⟨p,(hPB p.property).1⟩) z) c) ∧
          (∀ p : P, L w z (liftRows p) =
            coordinateFieldWordPartial w (G ⟨p,(hPB p.property).1⟩) z) ∧
          ∀ T : Y →L[ℝ] ℝ,
            (∀ c : P →₀ ℝ, T (e c) = Finsupp.linearCombination ℝ
              (fun p : P => coordinateFieldWordPartial w (G ⟨p,(hPB p.property).1⟩) z) c) →
            T = L w z) ∧
        (∀ w : List (Fin 3), ContDiffOn ℝ (∞ : ℕ∞ω) (L w) Z) ∧
        ∀ (w : List (Fin 3)) (z : R3), z ∈ Z →
          HasFDerivAt (L w)
            (coordinateExpansion (fun i : Fin 3 => L (i::w) z)) z := by
  classical
  intro ν R F Y liftRows e
  have hStaticFamily := exists_radiusTwo_canonical_rowSpan_word_evaluations
    hreg hcalc g hg K G hData η S hS hSupp hOne P hPB
    a₀ ha₀ ha₀1 Z hZ hZBall hEtaOne
  rcases hStaticFamily with ⟨C,hC,L,hStatic⟩
  have hZB : Z ⊆ (radiusTwoOpens : Set R3) := by
    intro z hz
    change z ∈ ball (0 : R3) 2
    exact ball_subset_ball (by linarith : 2*a₀ ≤ 2) (hZBall hz)
  have hZS : Z ⊆ S := by
    intro z hz
    apply hSupp 0
    apply subset_tsupport (η 0 : R3 → ℝ)
    change η 0 z ≠ 0
    rw [hEtaOne z hz]
    norm_num
  have hDense : DenseRange e := by
    simpa only [F] using denseRange_radiusTwo_restrictedRow_linearCombination
      K S P (fun p hp => (hPB hp).1)
  let A : List (Fin 3) → R3 → R3 →L[ℝ] (Y →L[ℝ] ℝ) := fun w z =>
    coordinateExpansion (fun i : Fin 3 => L (i::w) z)
  have hQuadratic := norm_radiusTwo_rowSpan_word_operator_remainder_le
    hreg hcalc g hg K G hData S P Z hPB hZ hConvex hZB hZS C hC L hDense
    (fun w z hz => (hStatic w z hz).1)
    (fun w z hz => (hStatic w z hz).2.1)
  have hDerivative (w : List (Fin 3)) (z : R3) (hz : z ∈ Z) :
      HasFDerivAt (L w) (A w z) z := by
    let Q : ℝ := 9 * C (w.length+2)
    have hQ : 0 ≤ Q := mul_nonneg (by norm_num) (hC _)
    apply HasFDerivAt.of_isLittleO
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    have hDen : 0 < Q+1 := by linarith
    have hRadius : 0 < ε/(Q+1) := div_pos hε hDen
    filter_upwards [hZ.mem_nhds hz, Metric.ball_mem_nhds z hRadius] with z' hz' hBall
    have hNorm : ‖z'-z‖ < ε/(Q+1) := mem_ball_iff_norm.mp hBall
    have hMul : Q * ‖z'-z‖ ≤ ε := by
      have h := (lt_div_iff₀ hDen).mp hNorm
      nlinarith [norm_nonneg (z'-z)]
    calc
      ‖L w z' - L w z - A w z (z'-z)‖ ≤ Q * ‖z'-z‖^2 := by
        simpa only [A,Q] using hQuadratic w z z' hz hz'
      _ ≤ ε * ‖z'-z‖ := by
        simpa only [pow_two,mul_assoc] using
          mul_le_mul_of_nonneg_right hMul (norm_nonneg (z'-z))
  refine ⟨C,hC,L,hStatic,?_,?_⟩
  · exact contDiffOn_wordFamily_of_hasFDerivAt_coordinateExpansion
      L Z hZ (fun w z hz => hDerivative w z hz)
  · intro w z hz
    exact hDerivative w z hz

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwo_smooth_rowSpan_word_evaluations
