import Calderon.DivergenceProductRule
import Calderon.CollaboratorUCPLocalOct17

/-! Actual local harmonic cutoff forcing for Main M1.
Full before-code expansion: UPFRONT-LOCAL-SMOOTH-HARMONIC-CUTOFF-v001.md. -/
set_option autoImplicit false
noncomputable section
open Metric Set Filter Topology
open scoped ContDiff
namespace OAI.AnisotropicCalderon

theorem Lop_cutoff_of_contDiffOn
    {D : Set R3} (hD : IsOpen D)
    {a : Fin 3 → Fin 3 → R3 → ℝ} (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    {eta u : R3 → ℝ} (heta : ContDiff ℝ ∞ eta)
    (hets : tsupport eta ⊆ D) (hu : ContDiffOn ℝ ∞ u D)
    (heq : ∀ x ∈ D, Lop a u x = 0) :
    ContDiff ℝ ∞ (fun x => eta x * u x) ∧
      ∀ x : R3, Lop a (fun y => eta y * u y) x =
        u x * Lop a eta x + ∑ i : Fin 3, ∑ j : Fin 3,
          (a i j x + a j i x) * pd i eta x * pd j u x := by
  have hprod : ContDiff ℝ ∞ (fun x => eta x * u x) :=
    UCP.contDiff_of_tsupport_subset hD (heta.contDiffOn.mul hu)
      (tsupport_mul_subset_left.trans hets)
  refine ⟨hprod, ?_⟩
  intro x
  have hLopCongr {v w : R3 → ℝ} (hvw : v =ᶠ[𝓝 x] w) : Lop a v x = Lop a w x := by
    change divCoeffGrad (fun y i j => a i j y) v x =
      divCoeffGrad (fun y i j => a i j y) w x
    exact UCP.divCoeffGrad_congr (Filter.EventuallyEq.refl _ _) hvw
  by_cases hx : x ∈ D
  · obtain ⟨epsilon, hepsilon, hball⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds hx)
    let chi : ContDiffBump x :=
      ⟨epsilon / 4, epsilon / 2, by positivity, by linarith⟩
    have hchi : tsupport (chi : R3 → ℝ) ⊆ D := by
      rw [chi.tsupport_eq]
      exact (closedBall_subset_ball (by change epsilon / 2 < epsilon; linarith)).trans hball
    let v : R3 → ℝ := fun y => chi y * u y
    have hv : ContDiff ℝ ∞ v :=
      UCP.contDiff_of_tsupport_subset hD (chi.contDiff.contDiffOn.mul hu)
        (tsupport_mul_subset_left.trans hchi)
    have hvu : v =ᶠ[𝓝 x] u := by
      filter_upwards [chi.eventuallyEq_one] with y hy
      change chi y * u y = u y
      simp only [hy, Pi.one_apply, one_mul]
    have hvalue : v x = u x := hvu.eq_of_nhds
    have hpd : ∀ i : Fin 3, pd i v x = pd i u x := by
      intro i
      unfold pd
      rw [hvu.fderiv_eq (𝕜 := ℝ)]
    have hPv : Lop a v x = 0 := (hLopCongr hvu).trans (heq x hx)
    have hproducts : (fun y => eta y * u y) =ᶠ[𝓝 x] (fun y => eta y * v y) := by
      filter_upwards [hvu] with y hy
      rw [hy]
    rw [hLopCongr hproducts, Lop_mul ha heta hv x, hPv, hvalue]
    simp only [mul_zero, zero_add, hpd]
  · have hxeta : x ∉ tsupport eta := fun h => hx (hets h)
    have heta0 : eta =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [(isClosed_tsupport eta).isOpen_compl.mem_nhds hxeta] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    have hprod0 : (fun y => eta y * u y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [heta0] with y hy
      rw [hy, zero_mul]
    have hLzero : Lop a (fun _ => (0 : ℝ)) x = 0 := by simp [Lop, pd]
    have hLeta : Lop a eta x = 0 := (hLopCongr heta0).trans hLzero
    have hLprod : Lop a (fun y => eta y * u y) x = 0 := (hLopCongr hprod0).trans hLzero
    have hpd : ∀ i : Fin 3, pd i eta x = 0 := by
      intro i
      unfold pd
      rw [heta0.fderiv_eq (𝕜 := ℝ)]
      simp
    rw [hLprod, hLeta]
    simp only [hpd, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, add_zero]

end OAI.AnisotropicCalderon

#print axioms OAI.AnisotropicCalderon.Lop_cutoff_of_contDiffOn
