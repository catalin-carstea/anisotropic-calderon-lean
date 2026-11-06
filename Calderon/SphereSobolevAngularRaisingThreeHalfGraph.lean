import Calderon.SphereSobolevAngularRaisingSingle
import Calderon.AngularShiftGraph
import Calderon.SharpRadialHarmonicCoefficientCore

/-! The canonical H3half raising graph. -/
set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology ENNReal
namespace OAI.AnisotropicCalderon.SphereHarmonic
open AngularShiftGraph HarmonicDerivativeOperator

attribute [local irreducible] sphereSobolevAngularCoordinateTransposeL

lemma sphereSobolevAngularCoordinateTransposeL_threeHalf_raisingGraph
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (i : Fin 3) (u : SphereSobolev (3/2 : ℝ)) :
    ((sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num) u),
     (sphereSobolevZeroEquiv hO hD).symm
      (sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
        (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i u))) ∈
        sphereRaisingGraph hF hO hD i := by
  let Z := sphereSobolevZeroEquiv hO hD
  let I : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev 0 :=
    sphereSobolevInclusionL (3/2 : ℝ) 0 (by norm_num)
  let J : SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev 0 :=
    sphereSobolevInclusionL (1/2 : ℝ) 0 (by norm_num)
  let A : SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev 0 :=
    J.comp (sphereSobolevAngularCoordinateTransposeL hF hO hD (3/2 : ℝ) i)
  have hDecode (k : ℕ) (v : harmonicSphereSubspace k) :
      Z.symm (sphereSobolevSingleL 0 k v) = (v : SphereL2) :=
    (congrArg Z.symm (sphereSobolevZeroEquiv_harmonic_subtype hO hD k v)).symm.trans
      (Z.symm_apply_apply (v : SphereL2))
  have hSingle (k : ℕ) (v : harmonicSphereSubspace k) :
      (Z.symm (I (sphereSobolevSingleL (3/2 : ℝ) k v)),
       Z.symm (A (sphereSobolevSingleL (3/2 : ℝ) k v))) ∈ sphereRaisingGraph hF hO hD i := by
    have hI : I (sphereSobolevSingleL (3/2 : ℝ) k v) = sphereSobolevSingleL 0 k v :=
      sphereSobolevInclusionL_single (3/2 : ℝ) 0 (by norm_num) k v
    have hNative := sphereSobolevAngularCoordinateTransposeL_single hF hO hD (3/2 : ℝ) i k v
    have hIndex : sphereSobolevSingleL ((3/2 : ℝ)-1) (k+1) (harmonicDerivativeAdjoint hF k i v) =
        sphereSobolevSingleL (1/2 : ℝ) (k+1) (harmonicDerivativeAdjoint hF k i v) := by
      have hw := congrArg (fun t : ℝ => SpectralWeightedGraph.besselWeight t (k+1))
        (show (3/2 : ℝ)-1 = (1/2 : ℝ) by norm_num)
      have hVector := congrArg (fun c : ℝ =>
        c • lp.single (E := fun n : ℕ => harmonicSphereSubspace n) 2 (k+1) (harmonicDerivativeAdjoint hF k i v)) hw
      simpa (config := { instances := true }) only
        [sphereSobolevSingleL,ContinuousLinearMap.smul_apply,
          lp.singleContinuousLinearMap_apply] using hVector
    have hA : A (sphereSobolevSingleL (3/2 : ℝ) k v) =
        sphereSobolevSingleL 0 (k+1) (harmonicDerivativeAdjoint hF k i v) :=
      (congrArg J (hNative.trans hIndex)).trans
        (sphereSobolevInclusionL_single (1/2 : ℝ) 0 (by norm_num) (k+1)
          (harmonicDerivativeAdjoint hF k i v))
    have hInput := (congrArg Z.symm hI).trans (hDecode k v)
    have hOutput := (congrArg Z.symm hA).trans
      (hDecode (k+1) (harmonicDerivativeAdjoint hF k i v))
    have hPair := congrArg₂ (fun a b : SphereL2 => (a,b)) hInput hOutput
    exact (congrArg (fun pair : SphereL2 × SphereL2 =>
      pair ∈ sphereRaisingGraph hF hO hD i) hPair).mpr
        (sphereRaisingGraph_single hF hO hD i k v)
  have hFinite (n : ℕ) :
      (Z.symm (I (sphereSobolevPartialSum (3/2 : ℝ) n u)),
       Z.symm (A (sphereSobolevPartialSum (3/2 : ℝ) n u))) ∈ sphereRaisingGraph hF hO hD i := by
    induction n with
    | zero =>
      have hz := (sphereRaisingGraph hF hO hD i).zero_mem
      change ((0 : SphereL2),(0 : SphereL2)) ∈ sphereRaisingGraph hF hO hD i at hz
      have hPartial : sphereSobolevPartialSum (3/2 : ℝ) 0 u = 0 := by
        unfold sphereSobolevPartialSum
        exact Finset.sum_range_zero _
      have hInput : Z.symm (I (sphereSobolevPartialSum (3/2 : ℝ) 0 u)) = 0 :=
        (congrArg (fun v : SphereSobolev (3/2 : ℝ) => Z.symm (I v)) hPartial).trans
          ((congrArg Z.symm I.map_zero).trans Z.symm.map_zero)
      have hOutput : Z.symm (A (sphereSobolevPartialSum (3/2 : ℝ) 0 u)) = 0 :=
        (congrArg (fun v : SphereSobolev (3/2 : ℝ) => Z.symm (A v)) hPartial).trans
          ((congrArg Z.symm A.map_zero).trans Z.symm.map_zero)
      have hPair := congrArg₂ (fun a b : SphereL2 => (a,b)) hInput hOutput
      exact (congrArg (fun pair : SphereL2 × SphereL2 =>
        pair ∈ sphereRaisingGraph hF hO hD i) hPair).mpr hz
    | succ n ih =>
      have h := (sphereRaisingGraph hF hO hD i).add_mem ih
        (hSingle n (sphereSobolevCoefficientL (3/2 : ℝ) n u))
      change (Z.symm (I (sphereSobolevPartialSum (3/2 : ℝ) n u)) +
          Z.symm (I (sphereSobolevSingleL (3/2 : ℝ) n (sphereSobolevCoefficientL (3/2 : ℝ) n u))),
        Z.symm (A (sphereSobolevPartialSum (3/2 : ℝ) n u)) +
          Z.symm (A (sphereSobolevSingleL (3/2 : ℝ) n (sphereSobolevCoefficientL (3/2 : ℝ) n u)))) ∈
            sphereRaisingGraph hF hO hD i at h
      simpa only [sphereSobolevPartialSum,Finset.sum_range_succ,map_add] using h
  have hI := (Z.symm.continuous.comp I.continuous).tendsto u |>.comp
    (tendsto_sphereSobolevPartialSum (3/2 : ℝ) u)
  have hA := (Z.symm.continuous.comp A.continuous).tendsto u |>.comp
    (tendsto_sphereSobolevPartialSum (3/2 : ℝ) u)
  exact (isClosed_sphereRaisingGraph hF hO hD i).mem_of_tendsto
    (hI.prodMk_nhds hA) (Filter.Eventually.of_forall hFinite)

end OAI.AnisotropicCalderon.SphereHarmonic

#print axioms OAI.AnisotropicCalderon.SphereHarmonic.sphereSobolevAngularCoordinateTransposeL_threeHalf_raisingGraph
