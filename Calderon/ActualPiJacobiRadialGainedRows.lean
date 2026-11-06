import Calderon.ActualJacobiAngularGainedRows
import Calderon.ActualAdjacentGainedFiniteFamilyCaps
import Calderon.ActualAdjacentGainedBracket

/-! Source-only Sol author candidate. Upfront: full-finite-assembly-before-v001.
The coefficient parameters in every Taylor primitive are frozen at the current
joint parameter, then the same-physical-point diagonal is taken. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualPiJacobiRadialGainedRows
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier
  ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints
  ActualJacobiAngularGainedRows
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

section Algebra
variable {E F N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup N] [NormedSpace ℝ N]

private lemma radialAngularPair_graph
    (I : E →L[ℝ] F) (J : F →L[ℝ] N) (sH : E →L[ℝ] F) (sL : F →L[ℝ] N)
    (AH : E →L[ℝ] F) (AL : F →L[ℝ] N) (NH : E →L[ℝ] E) (NL : F →L[ℝ] F)
    (D : E →L[ℝ] F) (G : E →L[ℝ] E)
    (hD : ∀ u, J (D u) = sL (AH u)-AL (sH u))
    (hA : ∀ u, J (AH u) = AL (I u))
    (hG : ∀ u, I (G u) = sH (NH u)-NL (sH u)) (u : E) :
    J ((D.comp NH + AH.comp G) u) = sL (AH (NH u))-AL (NL (sH u)) := by
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,map_add,
    hD,hA,hG,map_sub]
  abel

private lemma angularRadialPair_graph
    (J : F →L[ℝ] N) (RH : E →L[ℝ] F) (RL : F →L[ℝ] N)
    (aH : E →L[ℝ] F) (aL : F →L[ℝ] N) (NL : F →L[ℝ] F) (NN : N →L[ℝ] N)
    (C : E →L[ℝ] F) (G : F →L[ℝ] F)
    (hN : ∀ v, J (NL v) = NN (J v))
    (hC : ∀ u, J (C u) = aL (RH u)-RL (aH u))
    (hG : ∀ v, J (G v) = NN (RL v)-RL (NL v)) (u : E) :
    J ((NL.comp C + G.comp aH) u) = NN (aL (RH u))-RL (NL (aH u)) := by
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,map_add,
    hN,hC,hG,map_sub]
  abel
end Algebra

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "NH" => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NL" => nativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NN" => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
local notation "NJ3" => referenceJacobiBoundaryThreeHalfCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "NJ2" => referenceJacobiBoundaryCoefficientFamily g hg L y0 Φ B ε C ρ H a w hData
local notation "PiH" => referencePiThreeHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiN" => referencePiNegativeHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Th" => adjointHighRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Tl" => adjointHalfRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Sh" => sharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Sl" => lowerSharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Guard" => finiteRoomGuard hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Ω" => referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "QN" => jacobiJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Hh" => jacobiAngularOperatorHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Hl" => jacobiAngularOperatorLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "hh" => jacobiAngularReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "hl" => jacobiAngularReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Original Pi native coefficient jets on the exact retained witness set. -/
def piJets (δ0 : ℝ) (W : CoeffRoom δ0) (i : Fin 3) (t : Tpar) : SmoothCoefficientJets 3 :=
  commonSupportCoefficientFamily 3 (W.piScalar i) (W.piSmooth i)
    W.piSupport W.piCompact (W.piZero i) t
local notation "QP" => piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

def originalRadialHigh (i : Fin 3) (t : Tpar) : Hi →L[ℝ] Half := (Th t.1).comp (PiH i t)
def originalRadialLow (i : Fin 3) (t : Tpar) : Half →L[ℝ] Neg := (Tl t.1).comp (PiL i t)
def originalRadialReverseHigh (i : Fin 3) (t : Tpar) : Hi →L[ℝ] Half := (PiL i t).comp (Sh t.1)
def originalRadialReverseLow (i : Fin 3) (t : Tpar) : Half →L[ℝ] Neg := (PiN i t).comp (Sl t.1)
local notation "Rh" => originalRadialHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Rl" => originalRadialLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "sh" => originalRadialReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "sl" => originalRadialReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Actual frozen-coefficient sharp radial/Jacobi order-zero gain. -/
def sharpJacobiGain (δ0 : ℝ) (W : CoeffRoom δ0) (j n : Fin 3) (p : Pphys) : Hi →L[ℝ] Hi :=
  referenceHighSmoothMultiplierBoundaryCommutatorSecondRemainder
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (QN δ0 W j n p) p.1 p.2.1 p.2.2

/-- Actual Rsharp/H1 high band. The Pi and N coefficients are both current. -/
def radialAngularHigh (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (i j : Fin 3) (t : Tpar) : Hi →L[ℝ] Half :=
  ∑ n : Fin 3, (
    (raisingMixed hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg (QP δ0 W i t) n t.1).comp
        (NH (QN δ0 W j n t.1)) +
      (raisingHigh hF hO hD n).comp
        ((PiH i t).comp (sharpJacobiGain g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W j n t.1)))

/-- Actual H1sharp/R band, using the actual canonical radial/N half-gain family G. -/
def angularRadialHigh (hreg : FixedDirichletRegularity)
    (Gcoord : Fin 3 → Pphys → Half →L[ℝ] Half)
    (GN : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Half)
    (δ0 : ℝ) (W : CoeffRoom δ0) (i j : Fin 3) (t : Tpar) : Hi →L[ℝ] Half :=
  ∑ m : Fin 3, (
    (NL (smoothMultiplierLowerJets (QN δ0 W i m t.1))).comp
      (loweringMixed hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hg Gcoord (QP δ0 W j t) m t.1) -
      (GN i m t.1).comp ((PiL j t).comp (loweringHigh hF hO hD m)))

attribute [local irreducible] originalRadialHigh originalRadialLow originalRadialReverseHigh originalRadialReverseLow
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL
  loweringHigh loweringLow raisingHigh raisingLow


@[instance_reducible] private def piOriginalValueNormed : NormedAddCommGroup (Hi) := inferInstance
@[instance_reducible] private def piOriginalValueModule : NormedSpace ℝ (Hi) := inferInstance
@[instance_reducible] private def piOriginalHalfValueNormed : NormedAddCommGroup (Half) := inferInstance
@[instance_reducible] private def piOriginalHalfValueModule : NormedSpace ℝ (Half) := inferInstance
@[instance_reducible] private def piOriginalNegValueNormed : NormedAddCommGroup (Neg) := inferInstance
@[instance_reducible] private def piOriginalNegValueModule : NormedSpace ℝ (Neg) := inferInstance
@[instance_reducible] private def piOriginalMapNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def piOriginalMapModule : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def piOriginalHalfMapNormed : NormedAddCommGroup (Half →L[ℝ] Half) := inferInstance
@[instance_reducible] private def piOriginalHalfMapModule : NormedSpace ℝ (Half →L[ℝ] Half) := inferInstance
@[instance_reducible] private def piValueNormed : NormedAddCommGroup (Hi) := piOriginalValueNormed
attribute [local instance] piValueNormed
private theorem piValueNormed_canonical : piValueNormed = piOriginalValueNormed := rfl
@[instance_reducible] private def piValueModule : NormedSpace ℝ (Hi) := piOriginalValueModule
attribute [local instance] piValueModule
private theorem piValueModule_canonical : piValueModule = piOriginalValueModule := rfl
@[instance_reducible] private def piHalfValueNormed : NormedAddCommGroup (Half) := piOriginalHalfValueNormed
attribute [local instance] piHalfValueNormed
private theorem piHalfValueNormed_canonical : piHalfValueNormed = piOriginalHalfValueNormed := rfl
@[instance_reducible] private def piHalfValueModule : NormedSpace ℝ (Half) := piOriginalHalfValueModule
attribute [local instance] piHalfValueModule
private theorem piHalfValueModule_canonical : piHalfValueModule = piOriginalHalfValueModule := rfl
@[instance_reducible] private def piNegValueNormed : NormedAddCommGroup (Neg) := piOriginalNegValueNormed
attribute [local instance] piNegValueNormed
private theorem piNegValueNormed_canonical : piNegValueNormed = piOriginalNegValueNormed := rfl
@[instance_reducible] private def piNegValueModule : NormedSpace ℝ (Neg) := piOriginalNegValueModule
attribute [local instance] piNegValueModule
private theorem piNegValueModule_canonical : piNegValueModule = piOriginalNegValueModule := rfl
@[instance_reducible] private def piMapNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := piOriginalMapNormed
attribute [local instance] piMapNormed
private theorem piMapNormed_canonical : piMapNormed = piOriginalMapNormed := rfl
@[instance_reducible] private def piMapModule : NormedSpace ℝ (Hi →L[ℝ] Half) := piOriginalMapModule
attribute [local instance] piMapModule
private theorem piMapModule_canonical : piMapModule = piOriginalMapModule := rfl
@[instance_reducible] private def piHalfMapNormed : NormedAddCommGroup (Half →L[ℝ] Half) := piOriginalHalfMapNormed
attribute [local instance] piHalfMapNormed
private theorem piHalfMapNormed_canonical : piHalfMapNormed = piOriginalHalfMapNormed := rfl
@[instance_reducible] private def piHalfMapModule : NormedSpace ℝ (Half →L[ℝ] Half) := piOriginalHalfMapModule
attribute [local instance] piHalfMapModule
private theorem piHalfMapModule_canonical : piHalfMapModule = piOriginalHalfMapModule := rfl

/-- Native Pi/Jacobi commutation at Half, discharged by the same current germs. -/
private lemma pi_jacobi_half_comm (δ0 : ℝ) (W : CoeffRoom δ0) (i j n : Fin 3)
    (t : Tpar) (ht : t ∈ ParamRoom δ0) (v : Half) :
    PiL i t (NL (NJ2 j n t.1) v) = NL (NJ2 j n t.1) (PiL i t v) := by
  have hP := (W.piGerm i t ht).self_of_nhds
  have hN := (W.jacobiGerm j n t.1 ht.1).self_of_nhds
  have hComm := nativeHalfCoefficientMulL_lowerJets_comm_apply hcalc hF hO hD τ0
    (QP δ0 W i t) (QN δ0 W j n t.1) v
  simpa only [piJets,jacobiJets,hP.2.1,hN.2.1] using hComm

/-- The actual zero-order [Rsharp_i,N_jn] graph, with the coefficient frozen. -/
private theorem radialReverseJacobi_zero_graph
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (W : CoeffRoom δ0) (lam Lam dF : ℝ)
    (hFin : ∀ p ∈ commonRoom y0 ρ dF, Guard lam Lam p)
    (i j n : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ0) (htF : t.1 ∈ commonRoom y0 ρ dF)
    (hr : |t.1.2.2| < dF) (u : Hi) :
    IH (PiH i t (sharpJacobiGain g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W j n t.1 u)) =
      sh i t (NH (NJ3 j n t.1) u)-NL (NJ2 j n t.1) (sh i t u) := by
  have hP := (W.piGerm i t ht).self_of_nhds
  have hN := (W.jacobiGerm j n t.1 ht.1).self_of_nhds
  have hPiC (v : Hi) : IH (PiH i t v) = PiL i t (IH v) := by
    have hPiCurrent := v017_native_high_half hcalc hF hO hD τ0 (QP δ0 W i t) v
    simpa only [piJets,hP.1,hP.2.1] using hPiCurrent
  have hGS := sharpMultiplierRemainder_graph_of_guard hcalc hF hO hD τ0
    g L y0 Φ B ε C ρ H a w hData hreg hKernel lam Lam dF hFin
    t.1.1 htF.1 t.1.2.1 htF.2.1 t.1.2.2 hr (QN δ0 W j n t.1) u
  have hGSTyped : IH (sharpJacobiGain g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W j n t.1 u) =
      Sh t.1 (NH (NJ3 j n t.1) u)-NL (NJ2 j n t.1) (Sh t.1 u) := by
    simpa only [sharpJacobiGain,sharpRemainder,jacobiJets,hN.1,hN.2.1] using hGS
  have hComm := pi_jacobi_half_comm g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    δ0 W i j n t ht (Sh t.1 u)
  exact (hPiC _).trans ((congrArg (PiL i t) hGSTyped).trans (by
    simpa only [map_sub,originalRadialReverseHigh,ContinuousLinearMap.comp_apply,hComm]))


private def jacobiRadialHalfGainsFoldedContract (δ0 : ℝ) : Prop :=
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧
    ∃ GN : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Half,
      (∀ i m : Fin 3, ContDiffOn ℝ ∞ (GN i m) (commonRoom y0 ρ δ)) ∧
      (∀ i m : Fin 3, ∀ p ∈ commonRoom y0 ρ δ, ∀ v : Half,
        JL (GN i m p v) = Tl p (NL (NJ2 i m p) v)-NN (NJ2 i m p) (Tl p v)) ∧
      (∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ i m : Fin 3, ∀ n : ℕ, n ≤ N →
        ∀ p ∈ commonRoom y0 ρ δ,
          ‖iteratedFDerivWithin ℝ n (GN i m) (commonRoom y0 ρ δ) p‖ ≤ M)

attribute [local irreducible] jacobiRadialHalfGainsFoldedContract

private theorem jacobiRadialHalfGainsFoldedContract_proof
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    jacobiRadialHalfGainsFoldedContract (g:=g) (L:=L) (y0:=y0) (Φ:=Φ) (B:=B) (ε:=ε) (C:=C) (ρ:=ρ)
    (H:=H) (a:=a) (w:=w) (hData:=hData) (hg:=hg) (hcalc:=hcalc)
    (hF:=hF) (hO:=hO) (hD:=hD) (τ0:=τ0) δ0 := by
  classical
  have hJoint := exists_reference_commonRadius_adjointSmoothMultiplier_canonical_joint_jets
    (T := Pphys) g L y0 Φ B ε C ρ H a w hData hg hcalc hreg hF hO hD τ0
  obtain ⟨dN,hdN,hdNρ,_hdN1,hFamily⟩ := hJoint
  obtain ⟨lam,Lam,dF,_hlam,hdF,_hdFρ,hFin⟩ := exists_finiteRoomGuard
    hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg
  let δ := min δ0 (min dN dF)
  have hδ : 0 < δ := lt_min hδ0 (lt_min hdN hdF)
  have hSub0 : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ δ0 := commonRoom_mono y0 ρ (min_le_left _ _)
  have hSubN : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ dN :=
    commonRoom_mono y0 ρ ((min_le_right _ _).trans (min_le_left _ _))
  have hSubF : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ dF :=
    commonRoom_mono y0 ρ ((min_le_right _ _).trans (min_le_right _ _))
  have hRoom : commonRoom y0 ρ δ ⊆ Ω := fun p hp => (hFin p (hSubF hp)).2.2.1
  have hAll (i m : Fin 3) : ∃ G : Pphys × Pphys → Half →L[ℝ] Half,
      ContDiffOn ℝ ∞ G (commonRoom y0 ρ dN ×ˢ (Set.univ : Set Pphys)) ∧
      ∀ z ∈ commonRoom y0 ρ dN ×ˢ (Set.univ : Set Pphys), ∀ v : Half,
        JL (G z v) =
          (-realHalfOperatorAdjointL (secondTaylorRemainder (fun r : ℝ =>
            referenceSmoothMultiplierBoundaryCommutatorFamily g L y0 Φ B ε C ρ H a w hData
              hcalc hF hO hD τ0 (QN δ0 W i m z.2) (z.1.1,(z.1.2.1,r))) z.1.2.2)) (JL v) := by
    have hOwner := hFamily (W.jacobiScalar i m) (W.jacobiSmooth i m)
      (W.jacobiSupport i m) (W.jacobiCompact i m) (W.jacobiZero i m)
    obtain ⟨G,hGS,hGG,_hGC⟩ := hOwner
    exact ⟨G,hGS,fun z hz => (hGG z hz).2.1⟩
  choose G0 hG0S hG0Graph using hAll
  let GN : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Half := fun i m p => G0 i m (p,p)
  have hMap : MapsTo (fun p : Pphys => (p,p)) (commonRoom y0 ρ δ)
      (commonRoom y0 ρ dN ×ˢ (Set.univ : Set Pphys)) := fun p hp => ⟨hSubN hp,Set.mem_univ _⟩
  have hGSM (i m : Fin 3) : ContDiffOn ℝ ∞ (GN i m) (commonRoom y0 ρ δ) :=
    (hG0S i m).comp (contDiff_id.prodMk contDiff_id).contDiffOn hMap
  have hGraph (i m : Fin 3) (p : Pphys) (hp : p ∈ commonRoom y0 ρ δ) (v : Half) :
      JL (GN i m p v) = Tl p (NL (NJ2 i m p) v)-NN (NJ2 i m p) (Tl p v) := by
    have hSeg := segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoom p hp
    have hNative := hG0Graph i m (p,p) (hMap hp) v
    have hFac := (referenceAdjointHalfRadialSecondRemainder_smoothMultiplier_negative_factor
      g L y0 Φ B ε C ρ H a w hData (W.jacobiScalar i m) (W.jacobiSmooth i m)
      (W.jacobiSupport i m) (W.jacobiCompact i m) (W.jacobiZero i m)
      hcalc hF hO hD τ0 hKernel p.1 p.2.1 p.2.2 p hSeg).1 v
    have hId := (W.jacobiGerm i m p (hSub0 hp)).self_of_nhds
    have hFirst : JL (GN i m p v) =
        Tl p (NL (smoothMultiplierLowerJets (QN δ0 W i m p)) v)-
          NN (smoothMultiplierLowerJets (QN δ0 W i m p)) (Tl p v) := by
      simpa only [GN,jacobiJets,adjointHalfRemainder,ContinuousLinearMap.neg_apply]
        using hNative.trans (by
          simpa only [jacobiJets,adjointHalfRemainder,ContinuousLinearMap.neg_apply] using hFac.symm)
    simpa only [jacobiJets,hId.2.1,hId.2.2] using hFirst
  have hU : UniqueDiffOn ℝ (commonRoom y0 ρ δ) :=
    uniqueDiffOn_commonRoom y0 ρ hData.1.2.1 hδ
  unfold jacobiRadialHalfGainsFoldedContract
  refine ⟨δ,hδ,min_le_left _ _,((min_le_right _ _).trans (min_le_left _ _)).trans hdNρ,GN,hGSM,hGraph,?_⟩
  intro N
  let cap := v016_exists_uniform_cap_two (commonRoom y0 ρ δ)
    (isCompact_commonRoom y0 ρ δ) hU GN GN hGSM hGSM N
  let M : ℝ := Classical.choose cap
  have hM0 : 0 ≤ M := (Classical.choose_spec cap).1
  have hM := (Classical.choose_spec cap).2
  exact ⟨M,hM0,fun i m n hn p hp => (hM i m n hn p hp).1⟩


/-- Actual canonical radial/Jacobi half gains on the ordinary owner's exact N
witnesses. The joint coefficient parameter is frozen inside each Taylor integral
and then the same-physical-point diagonal is taken. -/
theorem exists_commonRoom_jacobi_radial_half_gains
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧
    ∃ GN : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Half,
      (∀ i m : Fin 3, ContDiffOn ℝ ∞ (GN i m) (commonRoom y0 ρ δ)) ∧
      (∀ i m : Fin 3, ∀ p ∈ commonRoom y0 ρ δ, ∀ v : Half,
        JL (GN i m p v) = Tl p (NL (NJ2 i m p) v)-NN (NJ2 i m p) (Tl p v)) ∧
      (∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ i m : Fin 3, ∀ n : ℕ, n ≤ N →
        ∀ p ∈ commonRoom y0 ρ δ,
          ‖iteratedFDerivWithin ℝ n (GN i m) (commonRoom y0 ρ δ) p‖ ≤ M) := by
  simpa only [jacobiRadialHalfGainsFoldedContract] using
    (jacobiRadialHalfGainsFoldedContract_proof (g:=g) (L:=L) (y0:=y0) (Φ:=Φ) (B:=B) (ε:=ε) (C:=C) (ρ:=ρ)
    (H:=H) (a:=a) (w:=w) (hData:=hData) (hg:=hg) (hcalc:=hcalc)
    (hF:=hF) (hO:=hO) (hD:=hD) (τ0:=τ0) hreg hKernel δ0 hδ0 W)


private lemma raisingMixed_current_graph
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (W : CoeffRoom δ0) (lam Lam : ℝ) (i n : Fin 3)
    (t : Tpar) (ht : t ∈ ParamRoom δ0)
    (hG0 : Guard lam Lam (t.1.1,(t.1.2.1,0)))
    (hCAS : ∀ u : Hi,
      JL (raisingCommutator hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg n t.1 u) =
        raisingLow hF hO hD n (Sh t.1 u)-Sl t.1 (raisingHigh hF hO hD n u)) (u : Hi) :
    JL (raisingMixed hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg
      (QP δ0 W i t) n t.1 u) = sl i t (raisingHigh hF hO hD n u)-raisingLow hF hO hD n (sh i t u) := by
  have hP := (W.piGerm i t ht).self_of_nhds
  have hRA := raisingPiGain_graph hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hKernel
    lam Lam (QP δ0 W i t) n t.1.1 ht.1.1 t.1.2.1 ht.1.2.1 hG0
  have hNcompat := v017_native_half_negative hcalc hF hO hD τ0
    (smoothMultiplierLowerJets (QP δ0 W i t))
  simp only [raisingMixed,ContinuousLinearMap.add_apply,ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.comp_apply,map_add,map_neg,hNcompat,hRA,hCAS,map_sub]
  simp only [originalRadialReverseHigh,originalRadialReverseLow,ContinuousLinearMap.comp_apply,
    piJets,hP.2.1,hP.2.2]
  abel


private lemma loweringMixed_current_graph
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (Gcoord : Fin 3 → Pphys → Half →L[ℝ] Half)
    (δ0 : ℝ) (W : CoeffRoom δ0) (lam Lam : ℝ) (m j : Fin 3)
    (t : Tpar) (ht : t ∈ ParamRoom δ0)
    (hG0 : Guard lam Lam (t.1.1,(t.1.2.1,0)))
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (t.1.1,(t.1.2.1,θ*t.1.2.2)) ∈ Ω)
    (hCaT : ∀ u : Hi,
      JL (loweringAngularHighCommutator hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg Gcoord m t.1 u) =
        loweringLow hF hO hD m (Th t.1 u)-Tl t.1 (loweringHigh hF hO hD m u)) (u : Hi) :
    JL (loweringMixed hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hg Gcoord
      (QP δ0 W j t) m t.1 u) = loweringLow hF hO hD m (Rh j t u)-Rl j t (loweringHigh hF hO hD m u) := by
  have hP := (W.piGerm j t ht).self_of_nhds
  have hLA := loweringPiGain_graph hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hg hKernel
    lam Lam (QP δ0 W j t) m t.1.1 ht.1.1 t.1.2.1 ht.1.2.1 hG0
  have hNative := mixed_lowering_cancellation IH JL
    (loweringAngularHighCommutator hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg Gcoord m t.1)
    (Th t.1) (Tl t.1) (NH (QP δ0 W j t)) (NL (smoothMultiplierLowerJets (QP δ0 W j t)))
    (loweringPiGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hg (QP δ0 W j t) m t.1.1 t.1.2.1)
    (loweringHigh hF hO hD m) (loweringLow hF hO hD m) hCaT
    (v016_actual_Th_compat hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg t.1 hSeg) hLA u
  simpa only [loweringMixed,piJets,hP.1,hP.2.1,originalRadialHigh,originalRadialLow,
    ContinuousLinearMap.comp_apply] using hNative

private theorem radialAngularHigh_current_graph
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (W : CoeffRoom δ0) (lam Lam dF : ℝ)
    (hFin : ∀ p ∈ commonRoom y0 ρ dF, Guard lam Lam p)
    (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ0) (htF : t.1 ∈ commonRoom y0 ρ dF)
    (hr : |t.1.2.2| < dF) (hG0 : Guard lam Lam (t.1.1,(t.1.2.1,0)))
    (hCAS : ∀ n : Fin 3, ∀ u : Hi,
      JL (raisingCommutator hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg n t.1 u) =
        raisingLow hF hO hD n (Sh t.1 u)-Sl t.1 (raisingHigh hF hO hD n u)) (u : Hi) :
    JL (radialAngularHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W i j t u) =
      sl i t (Hh j t.1 u)-Hl j t.1 (sh i t u) := by
  have hTerm (n : Fin 3) :
      JL (((raisingMixed hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg (QP δ0 W i t) n t.1).comp
          (NH (QN δ0 W j n t.1)) +
        (raisingHigh hF hO hD n).comp ((PiH i t).comp
          (sharpJacobiGain g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W j n t.1))) u) =
        sl i t (raisingHigh hF hO hD n (NH (NJ3 j n t.1) u))-
          raisingLow hF hO hD n (NL (NJ2 j n t.1) (sh i t u)) := by
    have hN := (W.jacobiGerm j n t.1 ht.1).self_of_nhds
    have hActualD := raisingMixed_current_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg hKernel δ0 W lam Lam i n t ht hG0 (hCAS n)
    have hActualG := radialReverseJacobi_zero_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg hKernel δ0 W lam Lam dF hFin i j n t ht htF hr
    have hActualA := v017_inclusion_raisingHigh hF hO hD n
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,map_add,
      hActualD,hActualA,hActualG,map_sub]
    simp only [jacobiJets,hN.1]
    abel

  have hSum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun n _ => hTerm n)
  have hLeft :
      JL (radialAngularHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W i j t u) =
      ∑ n : Fin 3, JL (((raisingMixed hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg (QP δ0 W i t) n t.1).comp
          (NH (QN δ0 W j n t.1)) +
        (raisingHigh hF hO hD n).comp ((PiH i t).comp
          (sharpJacobiGain g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W j n t.1))) u) := by
    simp only [radialAngularHigh,ContinuousLinearMap.sum_apply,map_sum]
  refine hLeft.trans (hSum.trans ?_)
  simp only [jacobiAngularOperatorHigh,jacobiAngularOperatorLow,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,map_sum,Finset.sum_sub_distrib]


private theorem angularRadialHigh_current_graph
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (Gcoord : Fin 3 → Pphys → Half →L[ℝ] Half) (GN : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Half)
    (δ0 : ℝ) (W : CoeffRoom δ0) (lam Lam : ℝ) (i j : Fin 3)
    (t : Tpar) (ht : t ∈ ParamRoom δ0) (hG0 : Guard lam Lam (t.1.1,(t.1.2.1,0)))
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (t.1.1,(t.1.2.1,θ*t.1.2.2)) ∈ Ω)
    (hCaT : ∀ m : Fin 3, ∀ u : Hi,
      JL (loweringAngularHighCommutator hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg Gcoord m t.1 u) =
        loweringLow hF hO hD m (Th t.1 u)-Tl t.1 (loweringHigh hF hO hD m u))
    (hGN : ∀ m : Fin 3, ∀ v : Half,
      JL (GN i m t.1 v) = Tl t.1 (NL (NJ2 i m t.1) v)-NN (NJ2 i m t.1) (Tl t.1 v)) (u : Hi) :
    JL (angularRadialHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg Gcoord GN δ0 W i j t u) =
      hl i t.1 (Rh j t u)-Rl j t (hh i t.1 u) := by
  have hTerm (m : Fin 3) :
      JL (((NL (smoothMultiplierLowerJets (QN δ0 W i m t.1))).comp
          (loweringMixed hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hg Gcoord (QP δ0 W j t) m t.1) -
        (GN i m t.1).comp ((PiL j t).comp (loweringHigh hF hO hD m))) u) =
        NN (NJ2 i m t.1) (loweringLow hF hO hD m (Rh j t u))-
          Rl j t (NL (NJ2 i m t.1) (loweringHigh hF hO hD m u)) := by
    have hN := (W.jacobiGerm i m t.1 ht.1).self_of_nhds
    have hNcompat := v017_native_half_negative hcalc hF hO hD τ0 (NJ2 i m t.1)
    have hZero (v : Half) : JL ((-(GN i m t.1).comp (PiL j t)) v) =
        NN (NJ2 i m t.1) (Rl j t v)-Rl j t (NL (NJ2 i m t.1) v) := by
      have hComm := (pi_jacobi_half_comm g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        δ0 W j i m t ht v).symm
      simp only [ContinuousLinearMap.neg_apply,ContinuousLinearMap.comp_apply,map_neg,hGN,
        originalRadialLow,map_sub,hComm]
      abel
    have hPair := angularRadialPair_graph JL (Rh j t) (Rl j t)
      (loweringHigh hF hO hD m) (loweringLow hF hO hD m)
      (NL (NJ2 i m t.1)) (NN (NJ2 i m t.1))
      (loweringMixed hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hg Gcoord (QP δ0 W j t) m t.1)
      (-(GN i m t.1).comp (PiL j t)) hNcompat
      (loweringMixed_current_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        hreg hKernel Gcoord δ0 W lam Lam m j t ht hG0 hSeg (hCaT m)) hZero u
    simpa only [jacobiJets,hN.2.1,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.neg_apply,sub_eq_add_neg] using hPair
  have hSum := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl (fun m _ => hTerm m)
  have hLeft :
      JL (angularRadialHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg Gcoord GN δ0 W i j t u) =
      ∑ m : Fin 3, JL (((NL (smoothMultiplierLowerJets (QN δ0 W i m t.1))).comp
          (loweringMixed hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hg Gcoord (QP δ0 W j t) m t.1) -
        (GN i m t.1).comp ((PiL j t).comp (loweringHigh hF hO hD m))) u) := by
    simp only [angularRadialHigh,ContinuousLinearMap.sum_apply,map_sum]
  refine hLeft.trans (hSum.trans ?_)
  simp only [jacobiAngularReverseHigh,jacobiAngularReverseLow,
    ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,map_sum,Finset.sum_sub_distrib]


private def actualPiJacobiMixedGraphsFoldedContract (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0) : Prop :=
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ commonRoom y0 ρ δ ⊆ Ω ∧
    ∃ Gcoord : Fin 3 → Pphys → Half →L[ℝ] Half,
    ∃ GN : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Half,
      (∀ m : Fin 3, ContDiffOn ℝ ∞ (Gcoord m) (commonRoom y0 ρ δ)) ∧
      (∀ i m : Fin 3, ContDiffOn ℝ ∞ (GN i m) (commonRoom y0 ρ δ)) ∧
      (∀ m : Fin 3, ContDiffOn ℝ ∞
        (loweringAngularHighCommutator hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg Gcoord m)
          (commonRoom y0 ρ δ)) ∧
      (∀ n : Fin 3, ContDiffOn ℝ ∞
        (raisingCommutator hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg n)
          (commonRoom y0 ρ δ)) ∧
      (∀ i j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi,
        JL (radialAngularHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W i j t u) =
          sl i t (Hh j t.1 u)-Hl j t.1 (sh i t u)) ∧
      (∀ i j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi,
        JL (angularRadialHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg Gcoord GN δ0 W i j t u) =
          hl i t.1 (Rh j t u)-Rl j t (hh i t.1 u))

attribute [local irreducible] actualPiJacobiMixedGraphsFoldedContract

private theorem actualPiJacobiMixedGraphsFoldedContract_proof
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    actualPiJacobiMixedGraphsFoldedContract (g:=g) (L:=L) (y0:=y0) (Φ:=Φ) (B:=B) (ε:=ε) (C:=C) (ρ:=ρ)
    (H:=H) (a:=a) (w:=w) (hData:=hData) (hg:=hg) (hcalc:=hcalc)
    (hF:=hF) (hO:=hO) (hD:=hD) (τ0:=τ0) hreg δ0 W := by
  classical
  obtain ⟨dA,hdA,hdAρ,hRoomA,Gcoord,hGcoordS,_hGcoordGraph,hCaT,_hGh,hCAS⟩ :=
    exists_reference_commonRadius_angularHigh_both_graph_caps
      hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hg hKernel
  obtain ⟨dN,hdN,_hdN0,_hdNρ,GN,hGNS,hGNG,_hGNC⟩ :=
    exists_commonRoom_jacobi_radial_half_gains g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg hKernel δ0 hδ0 W
  obtain ⟨lam,Lam,dF,_hlam,hdF,_hdFρ,hFin⟩ := exists_finiteRoomGuard
    hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg
  let δ := min δ0 (min dA (min dN (dF/2)))
  have hδ : 0 < δ := lt_min hδ0 (lt_min hdA (lt_min hdN (half_pos hdF)))
  have hδ0le : δ ≤ δ0 := min_le_left _ _
  have hδAle : δ ≤ dA := (min_le_right _ _).trans (min_le_left _ _)
  have hδNle : δ ≤ dN := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδFhalf : δ ≤ dF/2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδFle : δ ≤ dF := hδFhalf.trans (by linarith)
  have hSub0 := commonRoom_mono y0 ρ hδ0le
  have hSubA := commonRoom_mono y0 ρ hδAle
  have hSubN := commonRoom_mono y0 ρ hδNle
  have hSubF := commonRoom_mono y0 ρ hδFle
  have hRoom : commonRoom y0 ρ δ ⊆ Ω := hSubA.trans hRoomA
  have hG0 (p : Pphys) (hp : p ∈ commonRoom y0 ρ δ) : Guard lam Lam (p.1,(p.2.1,0)) :=
    hFin (p.1,(p.2.1,0)) ⟨hp.1,hp.2.1,⟨by linarith,by linarith⟩⟩
  unfold actualPiJacobiMixedGraphsFoldedContract
  refine ⟨δ,hδ,hδ0le,hδAle.trans hdAρ,hRoom,Gcoord,GN,
    fun m => (hGcoordS m).mono hSubA,
    fun i m => (hGNS i m).mono hSubN,
    fun m => (hCaT m).2.1.mono hSubA,
    fun n => (hCAS n).2.1.mono hSubA,?_,?_⟩
  · intro i j t ht u
    have hr : |t.1.2.2| < dF :=
      ((abs_le.mpr ht.1.2.2).trans hδFhalf).trans_lt (by linarith)
    exact radialAngularHigh_current_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg hKernel δ0 W lam Lam dF hFin i j t ⟨hSub0 ht.1,ht.2⟩ (hSubF ht.1) hr (hG0 t.1 ht.1)
      (fun n => (hCAS n).1 t.1 (hSubA ht.1)) u
  · intro i j t ht u
    have hSeg := segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoom t.1 ht.1
    exact angularRadialHigh_current_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg hKernel Gcoord GN δ0 W lam Lam i j t ⟨hSub0 ht.1,ht.2⟩ (hG0 t.1 ht.1) hSeg
      (fun m => (hCaT m).1 t.1 (hSubA ht.1))
      (fun m => hGNG i m t.1 (hSubN ht.1)) u


/-- The two actual radial/Jacobi mixed high graph families on ONE room and the
ordinary owner's retained Pi/N germs. Every graph premise is discharged here
from actual angular and canonical radial/N producers, never a new callback. -/
theorem exists_commonRoom_actualPiJacobi_mixed_high_graphs
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ commonRoom y0 ρ δ ⊆ Ω ∧
    ∃ Gcoord : Fin 3 → Pphys → Half →L[ℝ] Half,
    ∃ GN : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Half,
      (∀ m : Fin 3, ContDiffOn ℝ ∞ (Gcoord m) (commonRoom y0 ρ δ)) ∧
      (∀ i m : Fin 3, ContDiffOn ℝ ∞ (GN i m) (commonRoom y0 ρ δ)) ∧
      (∀ m : Fin 3, ContDiffOn ℝ ∞
        (loweringAngularHighCommutator hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg Gcoord m)
          (commonRoom y0 ρ δ)) ∧
      (∀ n : Fin 3, ContDiffOn ℝ ∞
        (raisingCommutator hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg n)
          (commonRoom y0 ρ δ)) ∧
      (∀ i j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi,
        JL (radialAngularHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W i j t u) =
          sl i t (Hh j t.1 u)-Hl j t.1 (sh i t u)) ∧
      (∀ i j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi,
        JL (angularRadialHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg Gcoord GN δ0 W i j t u) =
          hl i t.1 (Rh j t u)-Rl j t (hh i t.1 u)) := by
  simpa only [actualPiJacobiMixedGraphsFoldedContract] using
    (actualPiJacobiMixedGraphsFoldedContract_proof (g:=g) (L:=L) (y0:=y0) (Φ:=Φ) (B:=B) (ε:=ε) (C:=C) (ρ:=ρ)
    (H:=H) (a:=a) (w:=w) (hData:=hData) (hg:=hg) (hcalc:=hcalc)
    (hF:=hF) (hO:=hO) (hD:=hD) (τ0:=τ0) hreg hKernel δ0 hδ0 W)


/-- Joint smoothness of the two actual mixed bands, retaining the exact returned
Gcoord/GN/W. Conditions here are discharged by the actual producer immediately
below, not exposed as new analytic premises of the final owner. -/
private lemma actualPiJacobi_mixed_high_contDiffOn
    (hreg : FixedDirichletRegularity)
    (Gcoord : Fin 3 → Pphys → Half →L[ℝ] Half)
    (GN : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Half)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ lam Lam : ℝ) (hδ : 0 < δ)
    (hSub : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ δ0)
    (hRoom : commonRoom y0 ρ δ ⊆ Ω)
    (hFinite : ∀ p ∈ commonRoom y0 ρ δ, Guard lam Lam p)
    (hCaT : ∀ m : Fin 3, ContDiffOn ℝ ∞
      (loweringAngularHighCommutator hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg Gcoord m)
      (commonRoom y0 ρ δ))
    (hCAS : ∀ n : Fin 3, ContDiffOn ℝ ∞
      (raisingCommutator hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg n)
      (commonRoom y0 ρ δ))
    (hGN : ∀ i m : Fin 3, ContDiffOn ℝ ∞ (GN i m) (commonRoom y0 ρ δ)) :
    ∀ i j : Fin 3,
      ContDiffOn ℝ ∞ (radialAngularHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W i j)
        (ParamRoom δ) ∧
      ContDiffOn ℝ ∞ (angularRadialHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg Gcoord GN δ0 W i j)
        (ParamRoom δ) := by
  have hProj : MapsTo (Prod.fst : Tpar → Pphys) (ParamRoom δ) (commonRoom y0 ρ δ) :=
    fun t ht => ht.1
  have hG0 (t : Tpar) (ht : t ∈ ParamRoom δ) : Guard lam Lam (t.1.1,(t.1.2.1,0)) :=
    hFinite _ ⟨ht.1.1,ht.1.2.1,⟨by linarith,by linarith⟩⟩
  have hPiNative (i : Fin 3) :
      ContDiff ℝ ∞ (fun t => NH (QP δ0 W i t)) ∧
      ContDiff ℝ ∞ (fun t => NL (smoothMultiplierLowerJets (QP δ0 W i t))) := by
    refine ⟨contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
      (W.piScalar i) (W.piSmooth i) W.piSupport W.piCompact (W.piZero i),?_⟩
    simpa only [piJets,smoothMultiplierLowerJets_commonSupport] using
      contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
        (W.piScalar i) (W.piSmooth i) W.piSupport W.piCompact (W.piZero i)
  have hPiActual (i : Fin 3) : ContDiffOn ℝ ∞ (PiH i) (ParamRoom δ) ∧
      ContDiffOn ℝ ∞ (PiL i) (ParamRoom δ) := by
    refine ⟨fun t ht => ?_,fun t ht => ?_⟩
    · have hgerm := (W.piGerm i t ⟨hSub ht.1,ht.2⟩).mono (fun z hz => hz.1.symm)
      exact ((hPiNative i).1.contDiffAt.congr_of_eventuallyEq hgerm).contDiffWithinAt
    · have hgerm := (W.piGerm i t ⟨hSub ht.1,ht.2⟩).mono (fun z hz => hz.2.1.symm)
      exact ((hPiNative i).2.contDiffAt.congr_of_eventuallyEq hgerm).contDiffWithinAt
  have hNnative (i m : Fin 3) :
      ContDiffOn ℝ ∞ (fun t : Tpar => NH (QN δ0 W i m t.1)) (ParamRoom δ) ∧
      ContDiffOn ℝ ∞ (fun t : Tpar => NL (smoothMultiplierLowerJets (QN δ0 W i m t.1))) (ParamRoom δ) := by
    have hH := contDiff_nativeThreeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
      (W.jacobiScalar i m) (W.jacobiSmooth i m) (W.jacobiSupport i m) (W.jacobiCompact i m) (W.jacobiZero i m)
    have hL : ContDiff ℝ ∞ (fun p : Pphys => NL (smoothMultiplierLowerJets (QN δ0 W i m p))) := by
      simpa only [jacobiJets,smoothMultiplierLowerJets_commonSupport] using
        contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
          (W.jacobiScalar i m) (W.jacobiSmooth i m) (W.jacobiSupport i m) (W.jacobiCompact i m) (W.jacobiZero i m)
    exact ⟨(hH.comp contDiff_fst).contDiffOn,(hL.comp contDiff_fst).contDiffOn⟩
  have hRem (t : Tpar) (ht : t ∈ ParamRoom δ) :=
    contDiffAt_actualAngularRadialRemainder_families_of_segment hcalc hF hO hD τ0
      g L y0 Φ B ε C ρ H a w hData hreg t.1
      (segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoom t.1 ht.1)
  have hTh : ContDiffOn ℝ ∞ (fun t : Tpar => Th t.1) (ParamRoom δ) := fun t ht =>
    ((hRem t ht).1.comp (f := fun t : Tpar => t.1) t contDiffAt_fst).contDiffWithinAt
  have hSh : ContDiffOn ℝ ∞ (fun t : Tpar => Sh t.1) (ParamRoom δ) := fun t ht =>
    ((hRem t ht).2.2.1.comp (f := fun t : Tpar => t.1) t contDiffAt_fst).contDiffWithinAt
  have hU (i m : Fin 3) : ContDiffOn ℝ ∞ (fun t : Tpar =>
      loweringPiGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hg
        (QP δ0 W i t) m t.1.1 t.1.2.1) (ParamRoom δ) := by
    have hRaw : ContDiffOn ℝ ∞ (fun t : Tpar =>
        rawAdjointMultiplierZero hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hg
          (QP δ0 W i t) t.1.1 t.1.2.1) (ParamRoom δ) := fun t ht =>
      (contDiffAt_rawAdjointMultiplierZero_commonSupport hcalc hF hO hD τ0
        g L y0 Φ B ε C ρ H a w hData hg (W.piScalar i) (W.piSmooth i) W.piSupport W.piCompact (W.piZero i)
        (fun z : Tpar => z.1.1) contDiff_fst.fst (fun z : Tpar => z.1.2.1) contDiff_fst.snd.fst t
        (by unfold referenceGaugeNormalHighInvertibleLocus; exact (hG0 t ht).2.2.2.1)).contDiffWithinAt
    unfold loweringPiGain
    apply ContDiffOn.add
    · apply ContDiffOn.sum
      intro k hk
      exact contDiffOn_const.clm_comp
        (contDiff_nativeThreeHalfCoefficientMulL_rotationJets_commonSupport hcalc hF hO hD τ0
          (W.piScalar i) (W.piSmooth i) W.piSupport W.piCompact (W.piZero i) k m).contDiffOn
    · exact contDiffOn_const.clm_comp hRaw
  have hV (i n : Fin 3) : ContDiffOn ℝ ∞ (fun t : Tpar =>
      raisingPiGain hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
        (QP δ0 W i t) n t.1.1 t.1.2.1) (ParamRoom δ) := by
    have hRaw : ContDiffOn ℝ ∞ (fun t : Tpar =>
        rawHalfMultiplierZero hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
          (QP δ0 W i t) t.1.1 t.1.2.1) (ParamRoom δ) := fun t ht =>
      (contDiffAt_rawHalfMultiplierZero_commonSupport hcalc hF hO hD τ0
        g L y0 Φ B ε C ρ H a w hData (W.piScalar i) (W.piSmooth i) W.piSupport W.piCompact (W.piZero i)
        (fun z : Tpar => z.1.1) contDiff_fst.fst (fun z : Tpar => z.1.2.1) contDiff_fst.snd.fst t
        (hG0 t ht).2.2.1.1 (hG0 t ht).2.2.1.2.1).contDiffWithinAt
    unfold raisingPiGain
    apply ContDiffOn.sub
    · apply ContDiffOn.sum
      intro k hk
      exact (contDiff_nativeHalfCoefficientMulL_rotationJets_commonSupport hcalc hF hO hD τ0
        (W.piScalar i) (W.piSmooth i) W.piSupport W.piCompact (W.piZero i) k n).contDiffOn.clm_comp contDiffOn_const
    · exact hRaw.clm_comp contDiffOn_const
  have hLower (i m : Fin 3) : ContDiffOn ℝ ∞ (fun t : Tpar =>
      loweringMixed hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg hg Gcoord (QP δ0 W i t) m t.1)
      (ParamRoom δ) := by
    unfold loweringMixed
    exact (((hCaT m).comp contDiffOn_fst hProj).clm_comp (hPiNative i).1.contDiffOn).add
      (hTh.clm_comp (hU i m))
  have hRaise (i n : Fin 3) : ContDiffOn ℝ ∞ (fun t : Tpar =>
      raisingMixed hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg (QP δ0 W i t) n t.1)
      (ParamRoom δ) := by
    unfold raisingMixed
    exact (((hPiNative i).2.contDiffOn.clm_comp ((hCAS n).comp contDiffOn_fst hProj)).neg).add
      ((hV i n).clm_comp hSh)
  have hGS (j n : Fin 3) : ContDiffOn ℝ ∞ (fun t : Tpar =>
      sharpJacobiGain g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W j n t.1) (ParamRoom δ) := by
    intro t ht
    have hStrong : ∀ θ ∈ Icc (0 : ℝ) 1,
        (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 t.1.1 (t.1.2.1,θ*t.1.2.2)).IsInvertible ∧
        (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 t.1.1 (t.1.2.1,θ*t.1.2.2)).IsInvertible := by
      intro θ hθ
      have hθabs : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
      have hBound : |θ*t.1.2.2| ≤ δ :=
        ((by rw [abs_mul]; exact mul_le_mul_of_nonneg_right hθabs (abs_nonneg t.1.2.2)) :
          |θ*t.1.2.2| ≤ 1*|t.1.2.2|).trans (by simpa only [one_mul] using abs_le.mpr ht.1.2.2)
      exact (hFinite (t.1.1,(t.1.2.1,θ*t.1.2.2)) ⟨ht.1.1,ht.1.2.1,abs_le.mp hBound⟩).2.2.2.1
    have hJoint := contDiffAt_referenceHighSmoothMultiplierSecondRemainder_commonSupport_of_segment
      g L y0 Φ B ε C ρ H a w hData (W.jacobiScalar j n) (W.jacobiSmooth j n)
        (W.jacobiSupport j n) (W.jacobiCompact j n) (W.jacobiZero j n)
        hcalc hF hO hD τ0 t.1.1 t.1.2.1 t.1.2.2 t.1 hStrong
    have hDiag : ContDiffAt ℝ ∞ (fun z : Tpar => (z.1,z.1)) t := contDiffAt_fst.prodMk contDiffAt_fst
    simpa only [sharpJacobiGain,jacobiJets,Function.comp_def] using
      (hJoint.comp (f := fun z : Tpar => (z.1,z.1)) t hDiag).contDiffWithinAt
  intro i j
  refine ⟨?_,?_⟩
  · unfold radialAngularHigh
    apply ContDiffOn.sum
    intro n hn
    apply ContDiffOn.add
    · exact (hRaise i n).clm_comp (hNnative j n).1
    · exact contDiffOn_const.clm_comp ((hPiActual i).1.clm_comp (hGS j n))
  · unfold angularRadialHigh
    exact ContDiffOn.sum (fun m _ => ((hNnative i m).2.clm_comp (hLower j m)).sub
      (((hGN i m).comp contDiffOn_fst hProj).clm_comp ((hPiActual j).2.clm_comp contDiffOn_const)))

private def actualPiJacobiMixedSmoothFoldedContract (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0) : Prop :=
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ commonRoom y0 ρ δ ⊆ Ω ∧
    ∃ Gcoord : Fin 3 → Pphys → Half →L[ℝ] Half,
    ∃ GN : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Half,
      (∀ i j : Fin 3, ContDiffOn ℝ ∞
        (radialAngularHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W i j) (ParamRoom δ) ∧
        ContDiffOn ℝ ∞
        (angularRadialHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg Gcoord GN δ0 W i j) (ParamRoom δ)) ∧
      (∀ i j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi,
        JL (radialAngularHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W i j t u) =
          sl i t (Hh j t.1 u)-Hl j t.1 (sh i t u)) ∧
      (∀ i j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi,
        JL (angularRadialHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg Gcoord GN δ0 W i j t u) =
          hl i t.1 (Rh j t u)-Rl j t (hh i t.1 u))

attribute [local irreducible] actualPiJacobiMixedSmoothFoldedContract

private theorem actualPiJacobiMixedSmoothFoldedContract_proof
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    actualPiJacobiMixedSmoothFoldedContract (g:=g) (L:=L) (y0:=y0) (Φ:=Φ) (B:=B) (ε:=ε) (C:=C) (ρ:=ρ)
    (H:=H) (a:=a) (w:=w) (hData:=hData) (hg:=hg) (hcalc:=hcalc)
    (hF:=hF) (hO:=hO) (hD:=hD) (τ0:=τ0) hreg δ0 W := by
  obtain ⟨dM,hdM,hdM0,hdMρ,hRoomM,Gcoord,GN,_hGCS,hGNS,hCaT,hCAS,hRH,hHR⟩ :=
    exists_commonRoom_actualPiJacobi_mixed_high_graphs g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg hKernel δ0 hδ0 W
  obtain ⟨lam,Lam,dF,_hlam,hdF,_hdFρ,hFin⟩ := exists_finiteRoomGuard
    hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg
  let δ := min dM dF
  have hδ : 0 < δ := lt_min hdM hdF
  have hδM : δ ≤ dM := min_le_left _ _
  have hSubM := commonRoom_mono y0 ρ hδM
  have hSubF := commonRoom_mono y0 ρ (show δ ≤ dF from min_le_right _ _)
  have hRoom : commonRoom y0 ρ δ ⊆ Ω := hSubM.trans hRoomM
  unfold actualPiJacobiMixedSmoothFoldedContract
  refine ⟨δ,hδ,hδM.trans hdM0,hδM.trans hdMρ,hRoom,Gcoord,GN,?_,?_,?_⟩
  · exact actualPiJacobi_mixed_high_contDiffOn g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg Gcoord GN δ0 W δ lam Lam hδ
      (hSubM.trans (commonRoom_mono y0 ρ hdM0)) hRoom
      (fun p hp => hFin p (hSubF hp))
      (fun m => (hCaT m).mono hSubM) (fun n => (hCAS n).mono hSubM)
      (fun i m => (hGNS i m).mono hSubM)
  · exact fun i j t ht => hRH i j t ⟨hSubM ht.1,ht.2⟩
  · exact fun i j t ht => hHR i j t ⟨hSubM ht.1,ht.2⟩


/-- Actual mixed high graphs AND total joint smoothness, on the same retained W
and the same actual Gcoord/GN. No extra analytic callback is present. -/
theorem exists_commonRoom_actualPiJacobi_mixed_high_graphs_and_smooth
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ commonRoom y0 ρ δ ⊆ Ω ∧
    ∃ Gcoord : Fin 3 → Pphys → Half →L[ℝ] Half,
    ∃ GN : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Half,
      (∀ i j : Fin 3, ContDiffOn ℝ ∞
        (radialAngularHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W i j) (ParamRoom δ) ∧
        ContDiffOn ℝ ∞
        (angularRadialHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg Gcoord GN δ0 W i j) (ParamRoom δ)) ∧
      (∀ i j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi,
        JL (radialAngularHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W i j t u) =
          sl i t (Hh j t.1 u)-Hl j t.1 (sh i t u)) ∧
      (∀ i j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi,
        JL (angularRadialHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg Gcoord GN δ0 W i j t u) =
          hl i t.1 (Rh j t u)-Rl j t (hh i t.1 u)) := by
  simpa only [actualPiJacobiMixedSmoothFoldedContract] using
    (actualPiJacobiMixedSmoothFoldedContract_proof (g:=g) (L:=L) (y0:=y0) (Φ:=Φ) (B:=B) (ε:=ε) (C:=C) (ρ:=ρ)
    (H:=H) (a:=a) (w:=w) (hData:=hData) (hg:=hg) (hcalc:=hcalc)
    (hF:=hF) (hO:=hO) (hD:=hD) (τ0:=τ0) hreg hKernel δ0 hδ0 W)



variable (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
  (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))

def retainedAdjacentHigh (δ0 : ℝ) (W : CoeffRoom δ0) (i j : Fin 3) (t : Tpar) : Hi →L[ℝ] Half :=
  referenceAdjacentGainedCommutatorHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
    (QP δ0 W i t) (QP δ0 W j t) t.1.1 t.1.2.1 t.1.2.2

def retainedAdjacentLow (δ0 : ℝ) (W : CoeffRoom δ0) (i j : Fin 3) (t : Tpar) : Half →L[ℝ] Neg :=
  referenceAdjacentGainedCommutatorLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
    (QP δ0 W i t) (QP δ0 W j t) t.1.1 t.1.2.1 t.1.2.2
local notation "RRh" => retainedAdjacentHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "RRl" => retainedAdjacentLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room

private def retainedActualPiAdjacentRowsFoldedContract (δ0 : ℝ) (W : CoeffRoom δ0) : Prop :=
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧
      (∀ i j : Fin 3, ContDiffOn ℝ ∞ (RRh δ0 W i j) (ParamRoom δ) ∧
        ContDiffOn ℝ ∞ (RRl δ0 W i j) (ParamRoom δ)) ∧
      (∀ i j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi,
        JL (RRh δ0 W i j t u) = RRl δ0 W i j t (IH u) ∧
        JL (RRh δ0 W i j t u) = sl i t (Rh j t u)-Rl j t (sh i t u)) ∧
      (∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ i j : Fin 3, ∀ n : ℕ, n ≤ N → ∀ t ∈ ParamRoom δ,
        ‖iteratedFDerivWithin ℝ n (RRh δ0 W i j) (ParamRoom δ) t‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n (RRl δ0 W i j) (ParamRoom δ) t‖ ≤ M)

attribute [local irreducible] retainedActualPiAdjacentRowsFoldedContract

private theorem retainedActualPiAdjacentRowsFoldedContract_proof
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    retainedActualPiAdjacentRowsFoldedContract (g:=g) (L:=L) (y0:=y0) (Φ:=Φ) (B:=B) (ε:=ε) (C:=C) (ρ:=ρ)
    (H:=H) (a:=a) (w:=w) (hData:=hData) (hg:=hg) (hcalc:=hcalc)
    (hF:=hF) (hO:=hO) (hD:=hD) (τ0:=τ0) (Room:=Room) δ0 W := by
  classical
  obtain ⟨dC,hdC,hdCρ,hCFamily⟩ :=
    exists_reference_commonRadius_adjacentGainedCommutator_finite_family_caps_and_graph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel Tpar
  obtain ⟨dB,hdB,_hdBρ,hBGraph⟩ :=
    exists_reference_commonRadius_referenceAdjacentGainedCommutatorLow_bracket
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel
  let δ := min δ0 (min dC dB)
  have hδ : 0 < δ := lt_min hδ0 (lt_min hdC hdB)
  have hδC : δ ≤ dC := (min_le_right _ _).trans (min_le_left _ _)
  have hδB : δ ≤ dB := (min_le_right _ _).trans (min_le_right _ _)
  have hSub0 : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ δ0 := commonRoom_mono y0 ρ (min_le_left _ _)
  have hSubC : commonRoom y0 ρ δ ⊆ commonRoom y0 ρ dC := commonRoom_mono y0 ρ hδC
  have hPSub : ParamRoom δ ⊆ ParamRoom δ0 := fun t ht => ⟨hSub0 ht.1,ht.2⟩
  have hKt : IsCompact (ParamRoom δ0) :=
    (isCompact_commonRoom y0 ρ δ0).prod (isCompact_closedBall _ _)
  obtain ⟨_M,_hM0,hFamily⟩ := hCFamily W.piScalar W.piSmooth W.piSupport W.piCompact W.piZero
    (ParamRoom δ0) hKt
  have hJoint (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) :=
    hFamily i j t.1 (hSubC ht.1) t (hPSub ht) t (hPSub ht)
  have hDiag : ContDiff ℝ ∞ (fun t : Tpar => (t.1,(t,t))) :=
    contDiff_fst.prodMk (contDiff_id.prodMk contDiff_id)
  have hSm (i j : Fin 3) : ContDiffOn ℝ ∞ (RRh δ0 W i j) (ParamRoom δ) ∧
      ContDiffOn ℝ ∞ (RRl δ0 W i j) (ParamRoom δ) := by
    refine ⟨fun t ht => ?_,fun t ht => ?_⟩
    · have h := (hJoint i j t ht).1.comp (f := fun t : Tpar => (t.1,(t,t))) t hDiag.contDiffAt
      change ContDiffWithinAt ℝ ∞ (fun z : Tpar => RRh δ0 W i j z) (ParamRoom δ) t
      simpa only [retainedAdjacentHigh,piJets,Function.comp_def] using h.contDiffWithinAt
    · have h := (hJoint i j t ht).2.1.comp (f := fun t : Tpar => (t.1,(t,t))) t hDiag.contDiffAt
      change ContDiffWithinAt ℝ ∞ (fun z : Tpar => RRl δ0 W i j z) (ParamRoom δ) t
      simpa only [retainedAdjacentLow,piJets,Function.comp_def] using h.contDiffWithinAt
  have hGraph (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) (u : Hi) :
      JL (RRh δ0 W i j t u) = RRl δ0 W i j t (IH u) ∧
      JL (RRh δ0 W i j t u) = sl i t (Rh j t u)-Rl j t (sh i t u) := by
    have hCompat := (hJoint i j t ht).2.2.2.2 u
    have hPI := (W.piGerm i t (hPSub ht)).self_of_nhds
    have hPJ := (W.piGerm j t (hPSub ht)).self_of_nhds
    have hy : ‖t.1.2.1-y0‖ ≤ ρ := by simpa only [mem_closedBall,dist_eq_norm] using ht.1.2.1
    have hr : |t.1.2.2| ≤ dB := (abs_le.mpr ht.1.2.2).trans hδB
    have hRaw := hBGraph (W.piScalar i) (W.piSmooth i) W.piSupport W.piCompact (W.piZero i)
      t (QP δ0 W j t) t.1.1 ht.1.1 t.1.2.1 hy t.1.2.2 hr u
    have hActual : RRl δ0 W i j t (IH u) = sl i t (Rh j t u)-Rl j t (sh i t u) := by
      simpa only [retainedAdjacentLow,piJets,hPI.1,hPI.2.1,hPI.2.2,hPJ.1,hPJ.2.1,hPJ.2.2,
        originalRadialHigh,originalRadialLow,originalRadialReverseHigh,originalRadialReverseLow,
        adjointHighRemainder,adjointHalfRemainder,sharpRemainder,lowerSharpRemainder,
        ContinuousLinearMap.comp_apply] using hRaw
    exact ⟨hCompat,hCompat.trans hActual⟩
  have hK : IsCompact (ParamRoom δ) := (isCompact_commonRoom y0 ρ δ).prod (isCompact_closedBall _ _)
  have hU : UniqueDiffOn ℝ (ParamRoom δ) :=
    (uniqueDiffOn_commonRoom y0 ρ hData.1.2.1 hδ).prod
      (uniqueDiffOn_convex (convex_closedBall _ _)
        ⟨0,ball_subset_interior_closedBall (mem_ball_self one_pos)⟩)
  unfold retainedActualPiAdjacentRowsFoldedContract
  refine ⟨δ,hδ,min_le_left _ _,hδC.trans hdCρ,hSm,hGraph,?_⟩
  intro N
  exact v016_exists_uniform_cap_two (ParamRoom δ) hK hU (RRh δ0 W) (RRl δ0 W)
    (fun i j => (hSm i j).1) (fun i j => (hSm i j).2) N


/-- The full actual adjacent R/R graph and every finite joint jet cap, on the
ordinary owner's SAME Pi support witnesses and the diagonal (p,t,t). -/
theorem exists_commonRoom_retained_actualPi_adjacent_rows
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧
      (∀ i j : Fin 3, ContDiffOn ℝ ∞ (RRh δ0 W i j) (ParamRoom δ) ∧
        ContDiffOn ℝ ∞ (RRl δ0 W i j) (ParamRoom δ)) ∧
      (∀ i j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi,
        JL (RRh δ0 W i j t u) = RRl δ0 W i j t (IH u) ∧
        JL (RRh δ0 W i j t u) = sl i t (Rh j t u)-Rl j t (sh i t u)) ∧
      (∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ i j : Fin 3, ∀ n : ℕ, n ≤ N → ∀ t ∈ ParamRoom δ,
        ‖iteratedFDerivWithin ℝ n (RRh δ0 W i j) (ParamRoom δ) t‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n (RRl δ0 W i j) (ParamRoom δ) t‖ ≤ M) := by
  simpa only [retainedActualPiAdjacentRowsFoldedContract] using
    (retainedActualPiAdjacentRowsFoldedContract_proof (g:=g) (L:=L) (y0:=y0) (Φ:=Φ) (B:=B) (ε:=ε) (C:=C) (ρ:=ρ)
    (H:=H) (a:=a) (w:=w) (hData:=hData) (hg:=hg) (hcalc:=hcalc)
    (hF:=hF) (hO:=hO) (hD:=hD) (τ0:=τ0) (Room:=Room) hreg hKernel δ0 hδ0 W)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualPiJacobiRadialGainedRows
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualPiJacobiRadialGainedRows.exists_commonRoom_jacobi_radial_half_gains
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualPiJacobiRadialGainedRows.exists_commonRoom_actualPiJacobi_mixed_high_graphs
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualPiJacobiRadialGainedRows.exists_commonRoom_retained_actualPi_adjacent_rows
