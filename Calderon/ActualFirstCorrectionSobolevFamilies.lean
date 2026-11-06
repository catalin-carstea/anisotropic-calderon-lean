import Calderon.SphereSobolevCoordinateInclusion
import Calderon.ActualFirstCorrectionParameterJets

/-! Full upfront: EXPANSION-ActualFirstCorrectionSobolevFamilies-v001.md.
Existing actual finite-band F0, genuine inclusion and parameter-norm graphs. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Filter
open scoped Topology ContDiff ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SphereHilbertDecomposition BoundedAngularShift BoundedSpectralMultiplier
  OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
attribute [local irreducible] sphereSobolevRadialDriftL sphereSobolevRadialDriftAdjointL

lemma sphereSobolevInclusionL_radialDrift_single
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s t : ℝ) (hts : t ≤ s) (d : R3) (k : ℕ) (a : harmonicSphereSubspace k) :
    sphereSobolevInclusionL s t hts
      (sphereSobolevRadialDriftL hF hO hD s d (sphereSobolevSingleL s k a)) =
      sphereSobolevRadialDriftL hF hO hD t d
        (sphereSobolevInclusionL s t hts (sphereSobolevSingleL s k a)) := by
  cases k with
  | zero => rw [sphereSobolevRadialDriftL_constant,map_zero,
      sphereSobolevInclusionL_single,sphereSobolevRadialDriftL_constant]
  | succ k =>
    let I := sphereSobolevInclusionL s t hts
    calc
      _ = I (sphereSobolevSingleL s k (radialDriftBlockL hF d k a)) :=
        congrArg I (sphereSobolevRadialDriftL_single hF hO hD s d k a)
      _ = sphereSobolevSingleL t k (radialDriftBlockL hF d k a) :=
        sphereSobolevInclusionL_single s t hts k (radialDriftBlockL hF d k a)
      _ = sphereSobolevRadialDriftL hF hO hD t d (sphereSobolevSingleL t (k+1) a) :=
        (sphereSobolevRadialDriftL_single hF hO hD t d k a).symm
      _ = _ := congrArg (sphereSobolevRadialDriftL hF hO hD t d)
        (sphereSobolevInclusionL_single s t hts (k+1) a).symm


lemma sphereSobolevInclusionL_radialDrift
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s t : ℝ) (hts : t ≤ s) (d : R3) (u : SphereSobolev s) :
    sphereSobolevInclusionL s t hts (sphereSobolevRadialDriftL hF hO hD s d u) =
      sphereSobolevRadialDriftL hF hO hD t d (sphereSobolevInclusionL s t hts u) := by
  let A : SphereSobolev s →L[ℝ] SphereSobolev t :=
    (sphereSobolevInclusionL s t hts).comp (sphereSobolevRadialDriftL hF hO hD s d)
  let B : SphereSobolev s →L[ℝ] SphereSobolev t :=
    (sphereSobolevRadialDriftL hF hO hD t d).comp (sphereSobolevInclusionL s t hts)
  have hn (n : ℕ) : A (sphereSobolevPartialSum s n u) = B (sphereSobolevPartialSum s n u) := by
    unfold sphereSobolevPartialSum
    rw [map_sum,map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact sphereSobolevInclusionL_radialDrift_single hF hO hD s t hts d k
      (sphereSobolevCoefficientL s k u)
  have hA : Tendsto (fun n : ℕ => A (sphereSobolevPartialSum s n u)) atTop (𝓝 (A u)) :=
    (A.continuous.tendsto u).comp (tendsto_sphereSobolevPartialSum s u)
  have hB : Tendsto (fun n : ℕ => A (sphereSobolevPartialSum s n u)) atTop (𝓝 (B u)) := by
    simp_rw [hn]
    exact (B.continuous.tendsto u).comp (tendsto_sphereSobolevPartialSum s u)
  exact tendsto_nhds_unique hA hB

lemma sphereSobolevInclusionL_radialDriftAdjoint_single
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s t : ℝ) (hts : t ≤ s) (d : R3) (k : ℕ) (a : harmonicSphereSubspace k) :
    sphereSobolevInclusionL s t hts
      (sphereSobolevRadialDriftAdjointL hF hO hD s d (sphereSobolevSingleL s k a)) =
      sphereSobolevRadialDriftAdjointL hF hO hD t d
        (sphereSobolevInclusionL s t hts (sphereSobolevSingleL s k a)) := by
  rw [sphereSobolevRadialDriftAdjointL_single,sphereSobolevInclusionL_single,
    sphereSobolevInclusionL_single,sphereSobolevRadialDriftAdjointL_single]

lemma sphereSobolevInclusionL_radialDriftAdjoint
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s t : ℝ) (hts : t ≤ s) (d : R3) (u : SphereSobolev s) :
    sphereSobolevInclusionL s t hts (sphereSobolevRadialDriftAdjointL hF hO hD s d u) =
      sphereSobolevRadialDriftAdjointL hF hO hD t d (sphereSobolevInclusionL s t hts u) := by
  let A : SphereSobolev s →L[ℝ] SphereSobolev t :=
    (sphereSobolevInclusionL s t hts).comp (sphereSobolevRadialDriftAdjointL hF hO hD s d)
  let B : SphereSobolev s →L[ℝ] SphereSobolev t :=
    (sphereSobolevRadialDriftAdjointL hF hO hD t d).comp (sphereSobolevInclusionL s t hts)
  have hn (n : ℕ) : A (sphereSobolevPartialSum s n u) = B (sphereSobolevPartialSum s n u) := by
    unfold sphereSobolevPartialSum
    rw [map_sum,map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact sphereSobolevInclusionL_radialDriftAdjoint_single hF hO hD s t hts d k
      (sphereSobolevCoefficientL s k u)
  have hA : Tendsto (fun n : ℕ => A (sphereSobolevPartialSum s n u)) atTop (𝓝 (A u)) :=
    (A.continuous.tendsto u).comp (tendsto_sphereSobolevPartialSum s u)
  have hB : Tendsto (fun n : ℕ => A (sphereSobolevPartialSum s n u)) atTop (𝓝 (B u)) := by
    simp_rw [hn]
    exact (B.continuous.tendsto u).comp (tendsto_sphereSobolevPartialSum s u)
  exact tendsto_nhds_unique hA hB

theorem contDiff_sphereSobolevRadialDriftL (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (s : ℝ) :
    ContDiff ℝ ∞ (fun d : R3 => sphereSobolevRadialDriftL hF hO hD s d) := by
  have hA : ContDiff ℝ ∞ (fun d : R3 =>
      sphereSobolevRadialDriftAdjointL hF hO hD (-s) d) :=
    (contDiff_sphereSobolevRadialDriftAdjointL hF hO hD (-s)).of_le le_top
  have hAdj : ContDiff ℝ ∞ (fun A : SphereSobolev s →L[ℝ] SphereSobolev s =>
      ContinuousLinearMap.adjoint A) :=
    (ContinuousLinearMap.adjoint :
      (SphereSobolev s →L[ℝ] SphereSobolev s) ≃ₗᵢ[ℝ]
      (SphereSobolev s →L[ℝ] SphereSobolev s)).contDiff
  have hDouble (d : R3) :
      ContinuousLinearMap.adjoint (sphereSobolevRadialDriftAdjointL hF hO hD (-s) d) =
      sphereSobolevRadialDriftL hF hO hD s d := by
    simp only [sphereSobolevRadialDriftAdjointL,ContinuousLinearMap.adjoint_adjoint]
    have hEqualIndex (a b : ℝ) (hab : a = b) :
        (sphereSobolevRadialDriftL hF hO hD a d :
          SphereSobolev s →L[ℝ] SphereSobolev s) =
        (sphereSobolevRadialDriftL hF hO hD b d :
          SphereSobolev s →L[ℝ] SphereSobolev s) := by
      cases hab
      rfl
    exact hEqualIndex (-(-s)) s (neg_neg s)
  exact contDiffOn_univ.mp ((hAdj.comp hA).contDiffOn.congr
    (fun d hd => (hDouble d).symm))

end OAI.AnisotropicCalderon.SphereHarmonic
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open SphereHarmonic EnergyBridge ConnectionError
attribute [local irreducible] sphereSobolevRadialDriftL sphereSobolevRadialDriftAdjointL
  referenceCenterDrift

theorem contDiff_reference_sphereSobolevRadialDriftL
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) : ContDiff ℝ ∞ (fun p : ℝ × R3 =>
      sphereSobolevRadialDriftL hF hO hD s (referenceCenterDrift g L p.1 p.2)) :=
  (contDiff_sphereSobolevRadialDriftL hF hO hD s).comp
    (contDiff_referenceCenterDrift_joint g hg L)

theorem contDiff_reference_sphereSobolevRadialDriftAdjointL
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) : ContDiff ℝ ∞ (fun p : ℝ × R3 =>
      sphereSobolevRadialDriftAdjointL hF hO hD s (referenceCenterDrift g L p.1 p.2)) :=
  ((contDiff_sphereSobolevRadialDriftAdjointL hF hO hD s).of_le le_top).comp
    (contDiff_referenceCenterDrift_joint g hg L)

theorem exists_joint_referenceFirstCorrectionSobolev_operator_jet_bound
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (K : Set (ℝ × R3)) (hK : IsCompact K) (N : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, j ≤ N → ∀ p ∈ K,
      ‖iteratedFDeriv ℝ j (fun x : ℝ × R3 =>
        sphereSobolevRadialDriftL hF hO hD s (referenceCenterDrift g L x.1 x.2)) p‖ ≤ D ∧
      ‖iteratedFDeriv ℝ j (fun x : ℝ × R3 =>
        sphereSobolevRadialDriftAdjointL hF hO hD s (referenceCenterDrift g L x.1 x.2)) p‖ ≤ D := by
  trace "first-correction compact jets: proof entered"
  let V := SphereSobolev s →L[ℝ] SphereSobolev s
  let F : (ℝ × R3) → V := fun p =>
    sphereSobolevRadialDriftL hF hO hD s (referenceCenterDrift g L p.1 p.2)
  let G : (ℝ × R3) → V := fun p =>
    sphereSobolevRadialDriftAdjointL hF hO hD s (referenceCenterDrift g L p.1 p.2)
  have hFactual : ContDiff ℝ ∞ F :=
    contDiff_reference_sphereSobolevRadialDriftL g hg L hF hO hD s
  have hGactual : ContDiff ℝ ∞ G :=
    contDiff_reference_sphereSobolevRadialDriftAdjointL g hg L hF hO hD s
  trace "first-correction compact jets: typed families"
  let T : Bool → (ℝ × R3) → V := fun b => if b then G else F
  have hT (b : Bool) : ContDiff ℝ ∞ (T b) := by
    cases b with
    | false => exact hFactual
    | true => exact hGactual
  trace "first-correction compact jets: finite smooth family"
  have hBound : ∃ D : ℝ, 0 ≤ D ∧ ∀ j : ℕ, j ≤ N →
      ∀ p ∈ K, ∀ b : Bool, ‖iteratedFDeriv ℝ j (T b) p‖ ≤ D :=
    exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt
      (I := Bool) (X := ℝ × R3) (V := V) T K hK
        (fun b p hp => (hT b).contDiffAt) N
  trace "first-correction compact jets: uniform bound"
  obtain ⟨D,hDnonneg,hBound⟩ := hBound
  exact ⟨D,hDnonneg,fun j hj p hp =>
    ⟨hBound j hj p hp false,hBound j hj p hp true⟩⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevInclusionL_radialDrift_single
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevInclusionL_radialDrift
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevInclusionL_radialDriftAdjoint_single
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevInclusionL_radialDriftAdjoint
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.contDiff_sphereSobolevRadialDriftL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_reference_sphereSobolevRadialDriftL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_reference_sphereSobolevRadialDriftAdjointL
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_joint_referenceFirstCorrectionSobolev_operator_jet_bound
