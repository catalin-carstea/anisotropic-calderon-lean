import Calderon.ActualTwoMetricSeparatelySmoothSourceKernels
import Calderon.LocalCoordinateWordEqOnTransport
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp

set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge DirichletFamily ActualReferenceDDHigherGeometryJets ReferenceDensityBounds
open ActualReferenceLocalCoordinateWordJets

lemma norm_radiusTwo_poleSection_coordinateLine_remainder_le
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (K : ↥(radiusTwoOpens : Set R3) → RadiusTwoL2)
    (G : ↥(radiusTwoOpens : Set R3) → R3 → ℝ)
    (hData : IsRadiusTwoSymmetricInverseSourceKernel g hg K G)
    (z : (radiusTwoOpens : Set R3)) (O : Set R3) (hO : IsOpen O)
    (hOB : O ⊆ (radiusTwoOpens : Set R3) \ {(z : R3)})
    (M : ℝ) (hM : 0 ≤ M) (i : Fin 3)
    (hBound : ∀ q ∈ O,
      |coordinateFieldWordPartial [i,i] (radiusTwoKernelPoleSection G z) q| ≤ M)
    (p : R3) (t : ℝ) (ht : 0 ≤ t)
    (hLine : ∀ s ∈ Icc (0 : ℝ) t, p + s • coordinateDirection i ∈ O) :
    |radiusTwoKernelPoleSection G z (p + t • coordinateDirection i) -
      radiusTwoKernelPoleSection G z p -
      t * coordinateFieldWordPartial [i] (radiusTwoKernelPoleSection G z) p| ≤
        M * t^2 := by
  let f : R3 → ℝ := radiusTwoKernelPoleSection G z
  let v : R3 → ℝ := coordinateFieldWordPartial [i] f
  let e : R3 := coordinateDirection i
  let χ : ℝ → R3 := fun s => p + s • e
  let Φ : ℝ → ℝ := fun s => f (χ s)
  let Ψ : ℝ → ℝ := fun s => v (χ s)
  have hχ (s : ℝ) : χ s = p + s • coordinateDirection i := by
    exact WithLp.ofLp_injective (2 : ENNReal) (funext (fun j => by rfl))
  have hχO (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) : χ s ∈ O := by
    rw [hχ s]
    exact hLine s hs
  have hχZero : χ 0 = p := by
    apply WithLp.ofLp_injective (2 : ENNReal)
    funext j
    change p j + (0 : ℝ) * e j = p j
    simp only [zero_mul, add_zero]
  have hSmooth := IsRadiusTwoSymmetricInverseSourceKernel.separatelySmooth
    hreg hcalc g hg K G hData
  have hf : ContDiffOn ℝ ∞ f O := (hSmooth.2.2 z).mono hOB
  have hv : ContDiffOn ℝ ∞ v O :=
    contDiffOn_coordinateFieldWordPartial [i] f O hO hf
  have hPath (s : ℝ) : HasDerivAt χ e s := by
    have h := ((hasDerivAt_id s).smul_const e).const_add p
    simp only [one_smul] at h
    apply h.congr_of_eventuallyEq
    exact Eventually.of_forall (fun a =>
      WithLp.ofLp_injective (2 : ENNReal) (funext (fun j => by rfl)))
  have hPhi (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) : HasDerivAt Φ (Ψ s) s := by
    have hAt : DifferentiableAt ℝ f (χ s) :=
      (hf.contDiffAt (hO.mem_nhds (hχO s hs))).differentiableAt (by simp)
    exact hAt.hasFDerivAt.comp_hasDerivAt s (hPath s)
  have hPsi (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) :
      HasDerivAt Ψ (coordinateFieldWordPartial [i,i] f (χ s)) s := by
    have hAt : DifferentiableAt ℝ v (χ s) :=
      (hv.contDiffAt (hO.mem_nhds (hχO s hs))).differentiableAt (by simp)
    exact hAt.hasFDerivAt.comp_hasDerivAt s (hPath s)
  have hZero : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_rfl, ht⟩
  have hEnd : t ∈ Icc (0 : ℝ) t := ⟨ht, le_rfl⟩
  have hPsiLip (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) : |Ψ s - Ψ 0| ≤ M * s := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun a ha => (hPsi a ha).hasDerivWithinAt)
      (fun a ha => by simpa only [Real.norm_eq_abs] using hBound _ (hχO a ha))
      (convex_Icc (0 : ℝ) t) hZero hs
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hs.1] using h
  let H : ℝ → ℝ := fun s => Φ s - Φ 0 - s * Ψ 0
  have hH (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) :
      HasDerivAt H (Ψ s - Ψ 0) s := by
    exact ((hPhi s hs).sub_const (Φ 0)).sub (hasDerivAt_mul_const (Ψ 0))
  have hRemainder := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hH s hs).hasDerivWithinAt)
    (fun s hs => by
      have h := (hPsiLip s hs).trans (mul_le_mul_of_nonneg_left hs.2 hM)
      simpa only [Real.norm_eq_abs] using h)
    (convex_Icc (0 : ℝ) t) hZero hEnd
  simpa only [H, Φ, Ψ, hχZero, hχ t, v, e, f, zero_smul, add_zero, zero_mul, sub_self,
    sub_zero, Real.norm_eq_abs, abs_of_nonneg ht, pow_two, mul_assoc] using hRemainder

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.norm_radiusTwo_poleSection_coordinateLine_remainder_le
