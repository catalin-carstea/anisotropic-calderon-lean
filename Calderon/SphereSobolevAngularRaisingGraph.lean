import Calderon.SphereSobolevAngularRaisingSingle
import Calderon.AngularShiftGraph
import Calderon.SharpRadialHarmonicCoefficientCore

/-! Upfront: native-angular-raising-dictionary-author-oct16-v001/
EXPANSION-true-raising-graph-v003.md. True maximal raising graph for SAME A_1†. -/
set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
open AngularShiftGraph HarmonicDerivativeOperator

lemma sphereSobolevAngularCoordinateTransposeL_raisingGraph
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (i : Fin 3) (u : SphereSobolev 1) :
    ((sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL 1 0 (by norm_num) u),
     (sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevAngularCoordinateTransposeL hF hO hD 1 i u)) ∈
        sphereRaisingGraph hF hO hD i := by
  let Z := sphereSobolevZeroEquiv hO hD
  let I : SphereSobolev 1 →L[ℝ] SphereSobolev 0 := sphereSobolevInclusionL 1 0 (by norm_num)
  let A : SphereSobolev 1 →L[ℝ] SphereSobolev 0 :=
    sphereSobolevAngularCoordinateTransposeL hF hO hD 1 i
  have hDecode (k : ℕ) (v : harmonicSphereSubspace k) :
      Z.symm (sphereSobolevSingleL 0 k v) = (v : SphereL2) :=
    (congrArg Z.symm (sphereSobolevZeroEquiv_harmonic_subtype hO hD k v)).symm.trans
      (Z.symm_apply_apply (v : SphereL2))
  have hSingle (k : ℕ) (v : harmonicSphereSubspace k) :
      (Z.symm (I (sphereSobolevSingleL 1 k v)),
       Z.symm (A (sphereSobolevSingleL 1 k v))) ∈ sphereRaisingGraph hF hO hD i := by
    have hI : I (sphereSobolevSingleL 1 k v) = sphereSobolevSingleL 0 k v :=
      sphereSobolevInclusionL_single 1 0 (by norm_num) k v
    have hIndex : sphereSobolevSingleL ((1 : ℝ)-1) (k+1) (harmonicDerivativeAdjoint hF k i v) =
        sphereSobolevSingleL 0 (k+1) (harmonicDerivativeAdjoint hF k i v) := by
      have hw := congrArg (fun t : ℝ => SpectralWeightedGraph.besselWeight t (k+1))
        (show (1 : ℝ)-1 = 0 by norm_num)
      have hVector := congrArg (fun c : ℝ =>
        c • lp.single (E := fun n : ℕ => harmonicSphereSubspace n) 2 (k+1) (harmonicDerivativeAdjoint hF k i v)) hw
      simpa (config := { instances := true }) only
        [sphereSobolevSingleL,ContinuousLinearMap.smul_apply,
          lp.singleContinuousLinearMap_apply] using hVector
    have hA : A (sphereSobolevSingleL 1 k v) =
        sphereSobolevSingleL 0 (k+1) (harmonicDerivativeAdjoint hF k i v) :=
      (sphereSobolevAngularCoordinateTransposeL_single hF hO hD 1 i k v).trans hIndex
    rw [hI,hA,hDecode,hDecode]
    exact sphereRaisingGraph_single hF hO hD i k v
  have hFinite (n : ℕ) :
      (Z.symm (I (sphereSobolevPartialSum 1 n u)),
       Z.symm (A (sphereSobolevPartialSum 1 n u))) ∈ sphereRaisingGraph hF hO hD i := by
    induction n with
    | zero =>
      have hz := (sphereRaisingGraph hF hO hD i).zero_mem
      change ((0 : SphereL2),(0 : SphereL2)) ∈ sphereRaisingGraph hF hO hD i at hz
      simpa only [sphereSobolevPartialSum,Finset.sum_range_zero,map_zero] using hz
    | succ n ih =>
      have h := (sphereRaisingGraph hF hO hD i).add_mem ih
        (hSingle n (sphereSobolevCoefficientL 1 n u))
      change (Z.symm (I (sphereSobolevPartialSum 1 n u)) +
          Z.symm (I (sphereSobolevSingleL 1 n (sphereSobolevCoefficientL 1 n u))),
        Z.symm (A (sphereSobolevPartialSum 1 n u)) +
          Z.symm (A (sphereSobolevSingleL 1 n (sphereSobolevCoefficientL 1 n u)))) ∈
            sphereRaisingGraph hF hO hD i at h
      simpa only [sphereSobolevPartialSum,Finset.sum_range_succ,map_add] using h
  have hI := (Z.symm.continuous.comp I.continuous).tendsto u |>.comp
    (tendsto_sphereSobolevPartialSum 1 u)
  have hA := (Z.symm.continuous.comp A.continuous).tendsto u |>.comp
    (tendsto_sphereSobolevPartialSum 1 u)
  exact (isClosed_sphereRaisingGraph hF hO hD i).mem_of_tendsto
    (hI.prodMk_nhds hA) (Filter.Eventually.of_forall hFinite)

lemma zeroEquiv_symm_angularCoordinateTranspose_one_finite_packet
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (i : Fin 3) (s : Finset ℕ) (u : ∀ k, harmonicSphereSubspace k) :
    (sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevAngularCoordinateTransposeL hF hO hD 1 i
        (∑ k ∈ s, sphereSobolevSingleL 1 k (u k))) =
      ∑ k ∈ s, (harmonicDerivativeAdjoint hF k i (u k) : SphereL2) := by
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hIndex : sphereSobolevSingleL ((1 : ℝ)-1) (k+1) (harmonicDerivativeAdjoint hF k i (u k)) =
      sphereSobolevSingleL 0 (k+1) (harmonicDerivativeAdjoint hF k i (u k)) := by
    have hw := congrArg (fun t : ℝ => SpectralWeightedGraph.besselWeight t (k+1))
      (show (1 : ℝ)-1 = 0 by norm_num)
    have hVector := congrArg (fun c : ℝ =>
      c • lp.single (E := fun n : ℕ => harmonicSphereSubspace n) 2 (k+1) (harmonicDerivativeAdjoint hF k i (u k))) hw
    simpa (config := { instances := true }) only
      [sphereSobolevSingleL,ContinuousLinearMap.smul_apply,
        lp.singleContinuousLinearMap_apply] using hVector
  have h := (sphereSobolevAngularCoordinateTransposeL_single hF hO hD 1 i k (u k)).trans hIndex
  have hDecode := congrArg (sphereSobolevZeroEquiv hO hD).symm
    (sphereSobolevZeroEquiv_harmonic_subtype hO hD (k+1)
      (harmonicDerivativeAdjoint hF k i (u k)))
  exact (congrArg (sphereSobolevZeroEquiv hO hD).symm h).trans
    (hDecode.symm.trans ((sphereSobolevZeroEquiv hO hD).symm_apply_apply _))

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevAngularCoordinateTransposeL_raisingGraph
#print axioms OAI.AnisotropicCalderon.SphereHarmonic.zeroEquiv_symm_angularCoordinateTranspose_one_finite_packet
