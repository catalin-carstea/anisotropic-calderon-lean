import Calderon.ActualReferenceAdjointHighAngleDerivativeFamily
import Calderon.SignedTaylorFixedLinearTransport
import Calderon.LocalUniformTaylorRemainder
import Calderon.SequenceLpNaturalStructureData
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Calderon.ActualReferenceAdjointSignedRemainderCompatibility
import Calderon.SphereSobolevConormalRotationDerivative
import Mathlib.Topology.DenseEmbedding

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic SmoothSphereRotation
attribute [local irreducible] referenceAdjointThreeHalfRadialFamily
  referenceAdjointHalfRadialFamily referenceAdjointHighAngleDerivativeFamily
  referenceRadialEndpointInvertibleLocus secondTaylorRemainder
  sphereSobolevInclusionL sphereSobolevRotationL
local instance adjointAngleTaylorHalfComplete : CompleteSpace (SphereSobolev (1/2:ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
local instance adjointAngleTaylorNegativeComplete : CompleteSpace (SphereSobolev (-(1/2:ℝ))) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) := instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
  (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

lemma referenceAdjointHighAngleSecondRemainder_rotation_graph
    (hreg : FixedDirichletRegularity) (i j : Fin 3) (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0:ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (f : SphereSobolev (5/2:ℝ)) :
    sphereSobolevRotationL (1/2:ℝ) i j
      ((secondTaylorRemainder (fun z : ℝ => referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,z))) r)
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) f)) -
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      ((secondTaylorRemainder (fun z : ℝ => referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,z))) r)
        (sphereSobolevRotationL (5/2:ℝ) i j f)) =
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      ((secondTaylorRemainder (fun z : ℝ => referenceAdjointHighAngleDerivativeFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (q,(y,z))) r)
        (sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num) f)) := by
  let U : ℝ → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
    fun z => referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,z))
  let D : ℝ → SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
    fun z => referenceAdjointHighAngleDerivativeFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (q,(y,z))
  let I := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let Rhalf := sphereSobolevRotationL (1/2:ℝ) i j
  let Rraw := sphereSobolevRotationL (5/2:ℝ) i j
  let Ef : (SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
    Rhalf.comp (ContinuousLinearMap.apply ℝ (SphereSobolev (1/2:ℝ)) (I f)) -
      J.comp (ContinuousLinearMap.apply ℝ (SphereSobolev (1/2:ℝ)) (Rraw f))
  let Cf : (SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) →L[ℝ] SphereSobolev (-(1/2:ℝ)) :=
    J.comp (ContinuousLinearMap.apply ℝ (SphereSobolev (1/2:ℝ)) (I f))
  have hOpen := isOpen_referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hUS (θ : ℝ) (hθ : θ ∈ Icc (0:ℝ) 1) : ContDiffAt ℝ ∞ U (θ*r) :=
    ((contDiffOn_referenceAdjointThreeHalfRadialFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg).contDiffAt
        (hOpen.mem_nhds (hSegment θ hθ))).comp (f := fun z : ℝ => (q,(y,z))) (θ*r)
          (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hDS (θ : ℝ) (hθ : θ ∈ Icc (0:ℝ) 1) : ContDiffAt ℝ ∞ D (θ*r) :=
    ((contDiffOn_referenceAdjointHighAngleDerivativeFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j hreg).contDiffAt
        (hOpen.mem_nhds (hSegment θ hθ))).comp (f := fun z : ℝ => (q,(y,z))) (θ*r)
          (contDiffAt_const.prodMk (contDiffAt_const.prodMk contDiffAt_id))
  have hEq (θ : ℝ) (hθ : θ ∈ Icc (0:ℝ) 1) :
      (fun z => Ef (U z)) =ᶠ[𝓝 (θ*r)] (fun z => Cf (D z)) := by
    have hNear : ∀ᶠ z : ℝ in 𝓝 (θ*r), (q,(y,z)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 :=
      (continuousAt_const.prodMk (continuousAt_const.prodMk continuousAt_id)).eventually
        (hOpen.mem_nhds (hSegment θ hθ))
    filter_upwards [hNear] with z hz
    exact referenceAdjointHighAngleDerivativeFamily_rotation_graph
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j hreg (q,(y,z)) hz f
  have hGraph : Ef (secondTaylorRemainder U r) = Cf (secondTaylorRemainder D r) :=
    (secondTaylorRemainder_fixed_linear_map U Ef r hUS).trans
      ((secondTaylorRemainder_eq_of_locallyEq_on_segment
        (fun z => Ef (U z)) (fun z => Cf (D z)) r hEq).trans
          (secondTaylorRemainder_fixed_linear_map D Cf r hDS).symm)
  have hEf (A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) :
      Ef A = Rhalf (A (I f)) - J (A (Rraw f)) := rfl
  have hCf (A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ)) :
      Cf A = J (A (I f)) := rfl
  exact (hEf _).symm.trans (hGraph.trans (hCf _))

theorem exists_reference_commonRadius_adjointHighAngleSecondRemainder_bound
    (hreg : FixedDirichletRegularity) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ q ∈ Icc (0:ℝ) 1, ∀ y ∈ closedBall y0 ρ, ∀ r : ℝ, |r| ≤ δ →
        ∀ i j : Fin 3,
          ‖secondTaylorRemainder (fun z : ℝ => referenceAdjointHighAngleDerivativeFamily
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (q,(y,z))) r‖ ≤ C0/2 := by
  classical
  obtain ⟨δ,hδ,hδρ,hRoom⟩ := exists_reference_commonRadius_subset_radialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  let K : Set (ℝ × R3) := Icc (0:ℝ) 1 ×ˢ closedBall y0 ρ
  let F : Fin 3 → Fin 3 → ((ℝ × R3) × ℝ) →
      SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) :=
    fun i j z => referenceAdjointHighAngleDerivativeFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (z.1.1,(z.1.2,z.2))
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall y0 ρ)
  have hSmooth (i j : Fin 3) : ∀ z ∈ K ×ˢ Icc (-δ) δ, ContDiffAt ℝ ∞ (F i j) z := by
    intro z hz
    have hi : (z.1.1,(z.1.2,z.2)) ∈ referenceRadialEndpointInvertibleLocus
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 :=
      hRoom ⟨hz.1.1,hz.1.2,hz.2⟩
    have hD := (contDiffOn_referenceAdjointHighAngleDerivativeFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j hreg).contDiffAt
        ((isOpen_referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0).mem_nhds hi)
    exact hD.comp z (contDiffAt_fst.fst.prodMk (contDiffAt_fst.snd.prodMk contDiffAt_snd))
  have hBound (i j : Fin 3) := exists_compact_local_uniform_secondTaylorRemainder
    (F i j) K hK δ hδ.le (hSmooth i j)
  let Cij : Fin 3 → Fin 3 → ℝ := fun i j => Classical.choose (hBound i j)
  have hCij (i j : Fin 3) := Classical.choose_spec (hBound i j)
  have hNonneg (i j : Fin 3) : 0 ≤ Cij i j := (hCij i j).1
  have hRow (i : Fin 3) : 0 ≤ ∑ j : Fin 3, Cij i j :=
    Finset.sum_nonneg (fun j _ => hNonneg i j)
  refine ⟨δ,hδ,hδρ,∑ i : Fin 3, ∑ j : Fin 3, Cij i j,
    Finset.sum_nonneg (fun i _ => hRow i),?_⟩
  intro q hq y hy r hr i j
  have hOne : ‖secondTaylorRemainder (fun z : ℝ => referenceAdjointHighAngleDerivativeFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (q,(y,z))) r‖ ≤ Cij i j/2 :=
    ((hCij i j).2 (q,y) ⟨hq,hy⟩ r hr).2
  have hSum : Cij i j ≤ ∑ i' : Fin 3, ∑ j' : Fin 3, Cij i' j' :=
    (Finset.single_le_sum (fun j' _ => hNonneg i j') (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun i' _ => hRow i') (Finset.mem_univ i))
  exact hOne.trans (div_le_div_of_nonneg_right hSum (by norm_num : (0:ℝ) ≤ 2))


lemma referenceAdjointHighAngleSecondRemainder_completed_rotation_graph
    (hreg : FixedDirichletRegularity) (i j : Fin 3) (q : ℝ) (y : R3) (r : ℝ)
    (hSegment : ∀ θ ∈ Icc (0:ℝ) 1, (q,(y,θ*r)) ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)
    (u : SphereSobolev (3/2:ℝ)) :
    sphereSobolevRotationL (1/2:ℝ) i j
      ((secondTaylorRemainder (fun z : ℝ => referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,z))) r) u) -
      (secondTaylorRemainder (fun z : ℝ => referenceAdjointHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,z))) r)
        (sphereSobolevRotationL (3/2:ℝ) i j u) =
    sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
      ((secondTaylorRemainder (fun z : ℝ => referenceAdjointHighAngleDerivativeFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (q,(y,z))) r) u) := by
  let Th := secondTaylorRemainder (fun z : ℝ => referenceAdjointThreeHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,z))) r
  let Tl := secondTaylorRemainder (fun z : ℝ => referenceAdjointHalfRadialFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,z))) r
  let D2 := secondTaylorRemainder (fun z : ℝ => referenceAdjointHighAngleDerivativeFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j (q,(y,z))) r
  let I := sphereSobolevInclusionL (3/2:ℝ) (1/2:ℝ) (by norm_num)
  let Iraw := sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)
  let J := sphereSobolevInclusionL (1/2:ℝ) (-(1/2:ℝ)) (by norm_num)
  let Rraw := sphereSobolevRotationL (5/2:ℝ) i j
  let Rhigh := sphereSobolevRotationL (3/2:ℝ) i j
  let Rhalf := sphereSobolevRotationL (1/2:ℝ) i j
  let F : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) := Rhalf.comp Th - Tl.comp Rhigh
  let G : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) := J.comp D2
  have hCompat : J.comp Th = Tl.comp I :=
    referenceAdjointRadialSecondRemainder_high_half_compatibility
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg q y r hSegment
  have hRot (f : SphereSobolev (5/2:ℝ)) : I (Rraw f) = Rhigh (Iraw f) := by
    have hOp := sphereSobolevRotationL_inclusion (5/2:ℝ) (3/2:ℝ) (by norm_num) i j
    have hInclusion : sphereSobolevInclusionL ((5/2:ℝ)-1) ((3/2:ℝ)-1) (by norm_num) = I := by
      congr 1 <;> norm_num
    rw [hInclusion] at hOp
    exact (congrArg
      (fun A : SphereSobolev (5/2:ℝ) →L[ℝ] SphereSobolev (1/2:ℝ) => A f) hOp).symm
  have hRaw (f : SphereSobolev (5/2:ℝ)) : F (Iraw f) = G (Iraw f) := by
    have hPoint : J (Th (Rraw f)) = Tl (I (Rraw f)) :=
      congrArg (fun A : SphereSobolev (3/2:ℝ) →L[ℝ] SphereSobolev (-(1/2:ℝ)) => A (Rraw f)) hCompat
    have hRewrite : J (Th (Rraw f)) = Tl (Rhigh (Iraw f)) := hPoint.trans (congrArg Tl (hRot f))
    have hLeft : F (Iraw f) = Rhalf (Th (Iraw f)) - J (Th (Rraw f)) :=
      congrArg (fun z : SphereSobolev (-(1/2:ℝ)) => Rhalf (Th (Iraw f)) - z) hRewrite.symm
    exact hLeft.trans (referenceAdjointHighAngleSecondRemainder_rotation_graph
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg i j q y r hSegment f)
  have hFunctions : (F : SphereSobolev (3/2:ℝ) → SphereSobolev (-(1/2:ℝ))) ∘ Iraw =
      (G : SphereSobolev (3/2:ℝ) → SphereSobolev (-(1/2:ℝ))) ∘ Iraw := funext hRaw
  have hAll : (F : SphereSobolev (3/2:ℝ) → SphereSobolev (-(1/2:ℝ))) =
      (G : SphereSobolev (3/2:ℝ) → SphereSobolev (-(1/2:ℝ))) :=
    (denseRange_sphereSobolevInclusionL (5/2:ℝ) (3/2:ℝ) (by norm_num)).equalizer
      F.continuous G.continuous hFunctions
  have hFinal : F u = G u := congrFun hAll u
  simpa only [F,G,Th,Tl,D2,J,Rhigh,Rhalf,ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply] using hFinal

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointHighAngleSecondRemainder_rotation_graph
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_adjointHighAngleSecondRemainder_bound

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointHighAngleSecondRemainder_completed_rotation_graph
