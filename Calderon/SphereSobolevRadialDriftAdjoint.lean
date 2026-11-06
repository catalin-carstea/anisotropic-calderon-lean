import Calderon.SphereSobolevRadialDrift
import Calderon.SphereSobolevPairing
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology ENNReal InnerProductSpace
namespace OAI.AnisotropicCalderon.SphereHarmonic
open SphereHilbertDecomposition SpectralWeightedGraph BoundedSpectralMultiplier
  HarmonicDerivativeOperator BoundedAngularShift
  OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

/-! True probability-L2 pivot transpose on the concrete all-real completion.
Exact expansion, all public statements and complete definitions were sealed
before these bodies. Negative orders use normalized coordinates only. -/


def radialDriftAdjointBlockL (hF : SphereFischerInner) (d : R3) (k : ℕ) :
    harmonicSphereSubspace k →L[ℝ] harmonicSphereSubspace (k + 1) :=
  ContinuousLinearMap.adjoint (radialDriftBlockL hF d k)

theorem inner_radialDriftAdjointBlockL (hF : SphereFischerInner) (d : R3) (k : ℕ)
    (a : harmonicSphereSubspace k) (b : harmonicSphereSubspace (k + 1)) :
    ⟪radialDriftAdjointBlockL hF d k a, b⟫_ℝ =
      ⟪a, radialDriftBlockL hF d k b⟫_ℝ := by
  exact ContinuousLinearMap.adjoint_inner_left (radialDriftBlockL hF d k) b a

theorem radialDriftAdjointBlockL_eq (hF : SphereFischerInner) (d : R3) (k : ℕ) :
    radialDriftAdjointBlockL hF d k =
      (-(2 * ((k + 1 : ℕ) : ℝ) + 1)⁻¹) •
        ∑ i : Fin 3, (d i) • harmonicDerivativeAdjoint hF k i := by
  apply ContinuousLinearMap.ext
  intro a
  apply ext_inner_right ℝ
  intro b
  let r : ℝ := -(2 * ((k + 1 : ℕ) : ℝ) + 1)⁻¹
  have hblock : radialDriftBlockL hF d k b =
      r • ∑ i : Fin 3, (d i) • harmonicDerivative hF k i b := by
    simp only [radialDriftBlockL, r, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sum_apply, ContinuousLinearMap.neg_apply, neg_smul]
  have hraise :
      ((-(2 * ((k + 1 : ℕ) : ℝ) + 1)⁻¹) •
        ∑ i : Fin 3, (d i) • harmonicDerivativeAdjoint hF k i) a =
      r • ∑ i : Fin 3, (d i) • harmonicDerivativeAdjoint hF k i a := by
    simp only [r, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.neg_apply, neg_smul]
  have hinnerD :
      ⟪a, r • ∑ i : Fin 3, (d i) • harmonicDerivative hF k i b⟫_ℝ =
        r * ∑ i : Fin 3, (d i) * ⟪a, harmonicDerivative hF k i b⟫_ℝ := by
    rw [real_inner_smul_right (F := harmonicSphereSubspace k)]
    rw [inner_sum (𝕜 := ℝ) Finset.univ
      (fun i : Fin 3 => (d i) • harmonicDerivative hF k i b) a]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact real_inner_smul_right (F := harmonicSphereSubspace k)
      a (harmonicDerivative hF k i b) (d i)
  have hinnerR :
      ⟪r • ∑ i : Fin 3, (d i) • harmonicDerivativeAdjoint hF k i a, b⟫_ℝ =
        r * ∑ i : Fin 3, (d i) * ⟪harmonicDerivativeAdjoint hF k i a, b⟫_ℝ := by
    rw [real_inner_smul_left (F := harmonicSphereSubspace (k + 1))]
    rw [sum_inner (𝕜 := ℝ) Finset.univ
      (fun i : Fin 3 => (d i) • harmonicDerivativeAdjoint hF k i a) b]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact real_inner_smul_left (F := harmonicSphereSubspace (k + 1))
      (harmonicDerivativeAdjoint hF k i a) b (d i)
  calc
    ⟪radialDriftAdjointBlockL hF d k a, b⟫_ℝ =
        ⟪a, radialDriftBlockL hF d k b⟫_ℝ :=
      inner_radialDriftAdjointBlockL hF d k a b
    _ = ⟪a, r • ∑ i : Fin 3, (d i) • harmonicDerivative hF k i b⟫_ℝ :=
      congrArg (fun z : harmonicSphereSubspace k => ⟪a, z⟫_ℝ) hblock
    _ = r * ∑ i : Fin 3, (d i) * ⟪a, harmonicDerivative hF k i b⟫_ℝ := hinnerD
    _ = r * ∑ i : Fin 3, (d i) * ⟪harmonicDerivativeAdjoint hF k i a, b⟫_ℝ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact congrArg (fun z : ℝ => (d i) * z)
        (inner_harmonicDerivativeAdjoint hF k i a b).symm
    _ = ⟪r • ∑ i : Fin 3, (d i) • harmonicDerivativeAdjoint hF k i a, b⟫_ℝ :=
      hinnerR.symm
    _ = _ := congrArg (fun z : harmonicSphereSubspace (k + 1) => ⟪z, b⟫_ℝ) hraise.symm

def sphereSobolevRadialDriftAdjointL (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (d : R3) : SphereSobolev s →L[ℝ] SphereSobolev s :=
  ContinuousLinearMap.adjoint (sphereSobolevRadialDriftL hF hO hD (-s) d)

theorem sphereSobolevDualPairing_radialDriftAdjoint (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (d : R3) (u : SphereSobolev s) (v : SphereSobolev (-s)) :
    sphereSobolevDualPairing s (sphereSobolevRadialDriftAdjointL hF hO hD s d u) v =
      sphereSobolevDualPairing s u (sphereSobolevRadialDriftL hF hO hD (-s) d v) := by
  exact ContinuousLinearMap.adjoint_inner_left
    (sphereSobolevRadialDriftL hF hO hD (-s) d) v u

theorem norm_sphereSobolevRadialDriftAdjointL_le (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (d : R3) :
    ‖sphereSobolevRadialDriftAdjointL hF hO hD s d‖ ≤
      (2 * ∑ i : Fin 3, |d i|) * radialDriftSobolevBound (-s) := by
  unfold sphereSobolevRadialDriftAdjointL
  rw [LinearIsometryEquiv.norm_map]
  exact norm_sphereSobolevRadialDriftL_le hF hO hD (-s) d

theorem sphereSobolevRadialDriftAdjointL_single (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (s : ℝ) (d : R3) (k : ℕ) (a : harmonicSphereSubspace k) :
    sphereSobolevRadialDriftAdjointL hF hO hD s d (sphereSobolevSingleL s k a) =
      sphereSobolevSingleL s (k + 1) (radialDriftAdjointBlockL hF d k a) := by
  have hleft (j : ℕ) (b : harmonicSphereSubspace j) (v : SphereSobolev (-s)) :
      ⟪sphereSobolevSingleL s j b, v⟫_ℝ =
        ⟪b, sphereSobolevCoefficientL (-s) j v⟫_ℝ := by
    change ⟪besselWeight s j • lp.single (E := fun l : ℕ => harmonicSphereSubspace l) 2 j b, v⟫_ℝ =
      ⟪b, besselWeight (-(-s)) j • v j⟫_ℝ
    rw [neg_neg]
    calc
      _ = besselWeight s j * ⟪lp.single (E := fun l : ℕ => harmonicSphereSubspace l) 2 j b, v⟫_ℝ :=
        real_inner_smul_left _ _ _
      _ = besselWeight s j * ⟪b, v j⟫_ℝ :=
        congrArg (fun z : ℝ => besselWeight s j * z) (lp.inner_single_left (𝕜 := ℝ) j b v)
      _ = _ := (real_inner_smul_right b (v j) (besselWeight s j)).symm
  have hright (j : ℕ) (b : harmonicSphereSubspace j) (u : SphereSobolev s) :
      ⟪u, sphereSobolevSingleL (-s) j b⟫_ℝ =
        ⟪sphereSobolevCoefficientL s j u, b⟫_ℝ := by
    change ⟪u, besselWeight (-s) j • lp.single (E := fun l : ℕ => harmonicSphereSubspace l) 2 j b⟫_ℝ =
      ⟪besselWeight (-s) j • u j, b⟫_ℝ
    calc
      _ = besselWeight (-s) j * ⟪u, lp.single (E := fun l : ℕ => harmonicSphereSubspace l) 2 j b⟫_ℝ :=
        real_inner_smul_right _ _ _
      _ = besselWeight (-s) j * ⟪u j, b⟫_ℝ :=
        congrArg (fun z : ℝ => besselWeight (-s) j * z) (lp.inner_single_right (𝕜 := ℝ) j b u)
      _ = _ := (real_inner_smul_left (u j) b (besselWeight (-s) j)).symm
  apply sphereSobolev_ext s
  intro j
  apply ext_inner_right ℝ
  intro b
  have htranspose :
      ⟪sphereSobolevCoefficientL s j
        (sphereSobolevRadialDriftAdjointL hF hO hD s d (sphereSobolevSingleL s k a)), b⟫_ℝ =
      ⟪sphereSobolevSingleL s k a,
        sphereSobolevRadialDriftL hF hO hD (-s) d (sphereSobolevSingleL (-s) j b)⟫_ℝ := by
    calc
      _ = ⟪sphereSobolevRadialDriftAdjointL hF hO hD s d
          (sphereSobolevSingleL s k a), sphereSobolevSingleL (-s) j b⟫_ℝ :=
        (hright j b (sphereSobolevRadialDriftAdjointL hF hO hD s d
          (sphereSobolevSingleL s k a))).symm
      _ = _ := sphereSobolevDualPairing_radialDriftAdjoint hF hO hD s d
        (sphereSobolevSingleL s k a) (sphereSobolevSingleL (-s) j b)
  refine htranspose.trans ?_
  cases j with
  | zero =>
    calc
      _ = ⟪sphereSobolevSingleL s k a, (0 : SphereSobolev (-s))⟫_ℝ :=
        congrArg (fun z : SphereSobolev (-s) => ⟪sphereSobolevSingleL s k a, z⟫_ℝ)
          (sphereSobolevRadialDriftL_constant hF hO hD (-s) d b)
      _ = 0 := inner_zero_right _
      _ = ⟪(0 : harmonicSphereSubspace 0), b⟫_ℝ := (inner_zero_left b).symm
      _ = _ := congrArg (fun z : harmonicSphereSubspace 0 => ⟪z, b⟫_ℝ)
        (sphereSobolevCoefficientL_single_ne s (k + 1) 0 (by omega)
          (radialDriftAdjointBlockL hF d k a)).symm
  | succ m =>
    have hsingle :
        ⟪sphereSobolevSingleL s k a,
          sphereSobolevRadialDriftL hF hO hD (-s) d
            (sphereSobolevSingleL (-s) (m + 1) b)⟫_ℝ =
        ⟪a, sphereSobolevCoefficientL (-s) k
          (sphereSobolevSingleL (-s) m (radialDriftBlockL hF d m b))⟫_ℝ := by
      calc
        _ = ⟪sphereSobolevSingleL s k a,
            sphereSobolevSingleL (-s) m (radialDriftBlockL hF d m b)⟫_ℝ :=
          congrArg (fun z : SphereSobolev (-s) => ⟪sphereSobolevSingleL s k a, z⟫_ℝ)
            (sphereSobolevRadialDriftL_single hF hO hD (-s) d m b)
        _ = _ := hleft k a (sphereSobolevSingleL (-s) m (radialDriftBlockL hF d m b))
    refine hsingle.trans ?_
    by_cases hmk : m = k
    · subst m
      calc
        _ = ⟪a, radialDriftBlockL hF d k b⟫_ℝ :=
          congrArg (fun z : harmonicSphereSubspace k => ⟪a, z⟫_ℝ)
            (sphereSobolevCoefficientL_single_self (-s) k (radialDriftBlockL hF d k b))
        _ = ⟪radialDriftAdjointBlockL hF d k a, b⟫_ℝ :=
          (inner_radialDriftAdjointBlockL hF d k a b).symm
        _ = _ := congrArg (fun z : harmonicSphereSubspace (k + 1) => ⟪z, b⟫_ℝ)
          (sphereSobolevCoefficientL_single_self s (k + 1)
            (radialDriftAdjointBlockL hF d k a)).symm
    · calc
        _ = ⟪a, (0 : harmonicSphereSubspace k)⟫_ℝ :=
          congrArg (fun z : harmonicSphereSubspace k => ⟪a, z⟫_ℝ)
            (sphereSobolevCoefficientL_single_ne (-s) m k (Ne.symm hmk)
              (radialDriftBlockL hF d m b))
        _ = 0 := inner_zero_right _
        _ = ⟪(0 : harmonicSphereSubspace (m + 1)), b⟫_ℝ := (inner_zero_left b).symm
        _ = _ := congrArg (fun z : harmonicSphereSubspace (m + 1) => ⟪z, b⟫_ℝ)
          (sphereSobolevCoefficientL_single_ne s (k + 1) (m + 1) (by omega)
            (radialDriftAdjointBlockL hF d k a)).symm

theorem sphereSobolevRadialDriftL_zeroEquiv (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (d : R3) (u : SphereL2) :
    sphereSobolevRadialDriftL hF hO hD 0 d (sphereSobolevZeroEquiv hO hD u) =
      sphereSobolevZeroEquiv hO hD (radialDriftTraceL hF hO hD d u) := by
  have hM (v : SphereL2) : radialDriftSobolevMultiplier hO hD 0 v = v := by
    apply (sphereHarmonicDecomposition hO hD).injective
    apply lp.ext
    funext k
    change SpectralCoreRegularity.sphereHarmonicCoordinate hO hD k (radialDriftSobolevMultiplier hO hD 0 v) =
      SpectralCoreRegularity.sphereHarmonicCoordinate hO hD k v
    have hcoordinate := boundedSpectralMultiplier_mem hO hD (radialDriftSobolevRatio 0)
      (radialDriftSobolevBound 0)
      (le_trans (show (0 : ℝ) ≤ 1 by norm_num) (le_max_left _ _))
      (abs_radialDriftSobolevRatio_le 0) v k
    change SpectralCoreRegularity.sphereHarmonicCoordinate hO hD k (radialDriftSobolevMultiplier hO hD 0 v) =
      radialDriftSobolevRatio 0 k • SpectralCoreRegularity.sphereHarmonicCoordinate hO hD k v at hcoordinate
    have hr : radialDriftSobolevRatio 0 k = 1 := by simp [radialDriftSobolevRatio]
    simpa only [hr, one_smul] using hcoordinate
  change sphereHarmonicDecomposition hO hD
    (radialDriftTraceL hF hO hD d
      (radialDriftSobolevMultiplier hO hD 0
        ((sphereHarmonicDecomposition hO hD).symm (sphereHarmonicDecomposition hO hD u)))) =
    sphereHarmonicDecomposition hO hD (radialDriftTraceL hF hO hD d u)
  rw [LinearIsometryEquiv.symm_apply_apply, hM]

theorem sphereSobolevRadialDriftAdjointL_zeroEquiv (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (d : R3) (u : SphereL2) :
    sphereSobolevRadialDriftAdjointL hF hO hD 0 d (sphereSobolevZeroEquiv hO hD u) =
      sphereSobolevZeroEquiv hO hD (ContinuousLinearMap.adjoint
        (radialDriftTraceL hF hO hD d) u) := by
  let D := sphereSobolevZeroEquiv hO hD
  apply ext_inner_right ℝ
  intro v
  have hT : sphereSobolevRadialDriftL hF hO hD 0 d v =
      D (radialDriftTraceL hF hO hD d (D.symm v)) := by
    simpa only [D, LinearIsometryEquiv.apply_symm_apply] using
      sphereSobolevRadialDriftL_zeroEquiv hF hO hD d (D.symm v)
  have htranspose :
      ⟪sphereSobolevRadialDriftAdjointL hF hO hD 0 d (D u), v⟫_ℝ =
        ⟪D u, sphereSobolevRadialDriftL hF hO hD 0 d v⟫_ℝ := by
    have hp := sphereSobolevDualPairing_radialDriftAdjoint hF hO hD 0 d (D u) v
    change ⟪sphereSobolevRadialDriftAdjointL hF hO hD 0 d (D u), v⟫_ℝ =
      ⟪D u, sphereSobolevRadialDriftL hF hO hD (-(0 : ℝ)) d v⟫_ℝ at hp
    have hIndex (a b : ℝ) (hab : a = b) :
        (sphereSobolevRadialDriftL hF hO hD a d : SphereSobolev 0 →L[ℝ] SphereSobolev 0) =
        (sphereSobolevRadialDriftL hF hO hD b d : SphereSobolev 0 →L[ℝ] SphereSobolev 0) := by
      cases hab
      rfl
    exact hp.trans (congrArg (fun T : SphereSobolev 0 →L[ℝ] SphereSobolev 0 => ⟪D u, T v⟫_ℝ)
      (hIndex (-(0 : ℝ)) 0 (neg_zero : -(0 : ℝ) = 0)))
  calc
    _ = ⟪D u, sphereSobolevRadialDriftL hF hO hD 0 d v⟫_ℝ := htranspose
    _ = ⟪D u, D (radialDriftTraceL hF hO hD d (D.symm v))⟫_ℝ :=
      congrArg (fun z : SphereSobolev 0 => ⟪D u, z⟫_ℝ) hT
    _ = ⟪u, radialDriftTraceL hF hO hD d (D.symm v)⟫_ℝ :=
      D.inner_map_map u (radialDriftTraceL hF hO hD d (D.symm v))
    _ = ⟪ContinuousLinearMap.adjoint (radialDriftTraceL hF hO hD d) u, D.symm v⟫_ℝ :=
      (ContinuousLinearMap.adjoint_inner_left (radialDriftTraceL hF hO hD d) (D.symm v) u).symm
    _ = _ := by
      simpa only [LinearIsometryEquiv.apply_symm_apply] using
        (D.inner_map_map (ContinuousLinearMap.adjoint (radialDriftTraceL hF hO hD d) u)
          (D.symm v)).symm

theorem radialDriftTraceL_adjoint_subtype (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (d : R3) (k : ℕ) (a : harmonicSphereSubspace k) :
    ContinuousLinearMap.adjoint (radialDriftTraceL hF hO hD d) (a : SphereL2) =
      (radialDriftAdjointBlockL hF d k a : SphereL2) := by
  apply (sphereSobolevZeroEquiv hO hD).injective
  rw [← sphereSobolevRadialDriftAdjointL_zeroEquiv]
  change sphereSobolevRadialDriftAdjointL hF hO hD 0 d
    (sphereHarmonicDecomposition hO hD (a : SphereL2)) =
      sphereHarmonicDecomposition hO hD (radialDriftAdjointBlockL hF d k a : SphereL2)
  rw [sphereHarmonicDecomposition_subtype, sphereHarmonicDecomposition_subtype]
  simpa only [sphereSobolevSingleL, besselWeight_zero_order,
    ContinuousLinearMap.smul_apply, lp.singleContinuousLinearMap_apply, one_smul] using
      sphereSobolevRadialDriftAdjointL_single hF hO hD 0 d k a

end OAI.AnisotropicCalderon.SphereHarmonic
