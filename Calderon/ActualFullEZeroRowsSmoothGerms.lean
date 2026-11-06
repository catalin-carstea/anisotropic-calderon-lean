import Calderon.ActualPiJacobiRadialGainedRows
import Calderon.ActualFullECanonicalEndpoints
import Calderon.NativeThreeHalfBoundaryMultiplierLocalSmoothness

/-! Opus v046 author-only source. Full upfront mathematics: output/MATHEMATICS.md.
Not compiled, not reviewed. Independent of Root's `fullGainedHigh` and graph proof.
Complete ambient smooth germs, exact high/low compatibility and uniform finite
mixed jets for the literal K/Z zero row and the native z/E zero row, on the SAME
coefficient witness W returned by `exists_commonRoom_actual_fullE_ordinary_endpoints`. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEZeroRowsSmoothGerms
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier
  ActualAngularHighDraft ActualAngularPiDraft ActualFullEGainedEndpoints
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

section Algebra
variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Inclusion transport through `r • ∑ A B C` (same shape as the native zero words). -/
private lemma zeroRow_triple_compat
    (I : X →L[ℝ] Y) (r : ℝ)
    (AH BH CH : Fin 3 → X →L[ℝ] X) (AL BL CL : Fin 3 → Y →L[ℝ] Y)
    (hA : ∀ j u, I (AH j u)=AL j (I u))
    (hB : ∀ j u, I (BH j u)=BL j (I u))
    (hC : ∀ j u, I (CH j u)=CL j (I u)) (u : X) :
    I ((r • ∑ j : Fin 3,(AH j).comp ((BH j).comp (CH j))) u)=
      (r • ∑ j : Fin 3,(AL j).comp ((BL j).comp (CL j))) (I u) := by
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply,map_smul,map_sum,hA,hB,hC]

/-- Inclusion transport through the radial-plus-angular reverse `s + ∑ h`. -/
private lemma zeroRow_reversePair_compat
    (I : X →L[ℝ] Y) (J : Y →L[ℝ] Z)
    (RH : X →L[ℝ] Y) (RL : Y →L[ℝ] Z) (AH : Fin 3 → X →L[ℝ] Y) (AL : Fin 3 → Y →L[ℝ] Z)
    (hR : ∀ u, J (RH u)=RL (I u)) (hA : ∀ j u, J (AH j u)=AL j (I u)) (u : X) :
    J ((RH+∑ j : Fin 3,AH j) u)=(RL+∑ j : Fin 3,AL j) (I u) := by
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,map_add,map_sum,hR,hA]

/-- Exact ordered K/Z graph: `J (kH ZH - ZL kH) = (kL ZL - ZN kL) I`. -/
private lemma orderedKZ_graph
    (I : X →L[ℝ] Y) (J : Y →L[ℝ] Z) (kH : X →L[ℝ] Y) (kL : Y →L[ℝ] Z)
    (ZH : X →L[ℝ] X) (ZL : Y →L[ℝ] Y) (ZN : Z →L[ℝ] Z)
    (hk : ∀ u, J (kH u)=kL (I u)) (hH : ∀ u, I (ZH u)=ZL (I u))
    (hL : ∀ v, J (ZL v)=ZN (J v)) (u : X) :
    J ((kH.comp ZH-ZL.comp kH) u)=(kL.comp ZL-ZN.comp kL) (I u) := by
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,map_sub,hk,hH,hL]
end Algebra

section CommonSupport
variable (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

/-- Pointwise ambient content of the (private) printed `native_commonSupport_contDiff`,
rebuilt from public APIs: the H^{3/2} part from the printed
`contDiffAt_nativeThreeHalfCoefficientMulL_of_joint_on_open` with `S = univ`. -/
theorem commonSupport_native_contDiffAt {P : Type} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [FiniteDimensional ℝ P] (m : P × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p x, x ∉ K → m (p,x)=0) (p0 : P) :
    ContDiffAt ℝ ∞ (fun p => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
      (commonSupportCoefficientFamily 3 m hm K hK hz p)) p0 ∧
    ContDiffAt ℝ ∞ (fun p => nativeHalfCoefficientMulL hcalc hF hO hD τ0
      (smoothMultiplierLowerJets (commonSupportCoefficientFamily 3 m hm K hK hz p))) p0 ∧
    ContDiffAt ℝ ∞ (fun p => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
      (smoothMultiplierLowerJets (commonSupportCoefficientFamily 3 m hm K hK hz p))) p0 := by
  have hh : ContDiffAt ℝ ∞ (fun p => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
      (commonSupportCoefficientFamily 3 m hm K hK hz p)) p0 :=
    contDiffAt_nativeThreeHalfCoefficientMulL_of_joint_on_open hcalc hF hO hD τ0
      m univ isOpen_univ hm.contDiffOn
      (fun p => commonSupportCoefficientFamily 3 m hm K hK hz p)
      (fun p _ x => by
        change coefficientValue 3 (commonSupportCoefficientFamily 3 m hm K hK hz p) x.val =
          m (p,x.val)
        rw [coefficientValue_commonSupportCoefficientFamily])
      p0 (fun _ => mem_univ _)
  have hl : ContDiff ℝ ∞ (fun p => nativeHalfCoefficientMulL hcalc hF hO hD τ0
      (smoothMultiplierLowerJets (commonSupportCoefficientFamily 3 m hm K hK hz p))) := by
    simpa only [smoothMultiplierLowerJets_commonSupport] using
      (contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0 m hm K hK hz)
  have hAdj : ContDiff ℝ ∞ (fun A : Half →L[ℝ] Half => realHalfOperatorAdjointL A) :=
    ContinuousLinearMap.contDiff _
  have hn : ContDiff ℝ ∞ (fun p => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
      (smoothMultiplierLowerJets (commonSupportCoefficientFamily 3 m hm K hK hz p))) := by
    simpa only [nativeNegativeHalfCoefficientMulL,Function.comp_def] using hAdj.comp hl
  exact ⟨hh,hl.contDiffAt,hn.contDiffAt⟩
end CommonSupport

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

local notation "NJ3" => referenceJacobiBoundaryThreeHalfCoefficientFamily
  g hg L y0 Φ B ε C ρ H a w hData
local notation "NJ2" => referenceJacobiBoundaryCoefficientFamily
  g hg L y0 Φ B ε C ρ H a w hData
local notation "NH" i:max j:max p:max => nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (NJ3 i j p)
local notation "NL" i:max j:max p:max => nativeHalfCoefficientMulL hcalc hF hO hD τ0 (NJ2 i j p)
local notation "NN" i:max j:max p:max => nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (NJ2 i j p)
local notation "PiH" => referencePiThreeHalfMultiplier
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiN" => referencePiNegativeHalfMultiplier
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Sh" => sharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Sl" => lowerSharpRemainder hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData
local notation "Ω" => referenceRadialEndpointInvertibleLocus
  g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "Mh" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (3/2 : ℝ) (EuclideanSpace.single j 1)
local notation "Ml" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (1/2 : ℝ) (EuclideanSpace.single j 1)
local notation "Mn" j:max => sphereSobolevLinearCoordinateMulL hF hO hD (-(1/2 : ℝ)) (EuclideanSpace.single j 1)
local notation "Dr" s:max p:max => sphereSobolevRadialDriftAdjointL hF hO hD s (referenceCenterDrift g L p.1 p.2.1)
local notation "ZH" => zeroCorrectionHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZL" => zeroCorrectionHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZN" => zeroCorrectionNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zEh" => zeroReverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zEl" => zeroReverseELow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)

/-- Literal radial-plus-angular reverse part `k^h = Pi^l Sh + ∑ N^l a^h` (no H0 term). -/
def zeroRowReverseHigh (i : Fin 3) (t : Tpar) : Hi →L[ℝ] Half :=
  (PiL i t).comp (Sh t.1) + ∑ j : Fin 3, (NL i j t.1).comp (loweringHigh hF hO hD j)
/-- Its genuine low endpoint `k^l = Pi^n Sl + ∑ N^n a^l`. -/
def zeroRowReverseLow (i : Fin 3) (t : Tpar) : Half →L[ℝ] Neg :=
  (PiN i t).comp (Sl t.1) + ∑ j : Fin 3, (NN i j t.1).comp (loweringLow hF hO hD j)

local notation "kH" => zeroRowReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "kL" => zeroRowReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- The literal complete high K/Z row `k^h_i Z^Hi_j - Z^Half_j k^h_i`. -/
def zeroCorrectionKHigh (i j : Fin 3) (t : Tpar) : Hi →L[ℝ] Half :=
  (kH i t).comp (ZH j t.1) - (ZL j t.1).comp (kH i t)
/-- The genuine paired low K/Z row `k^l_i Z^Half_j - Z^Neg_j k^l_i` (native `Z^Neg`). -/
def zeroCorrectionKLow (i j : Fin 3) (t : Tpar) : Half →L[ℝ] Neg :=
  (kL i t).comp (ZL j t.1) - (ZN j t.1).comp (kL i t)

local notation "KZh" => zeroCorrectionKHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "KZl" => zeroCorrectionKLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-! ### Exact inclusions of the literal zero words (all physical p). -/

private lemma zeroRow_jacobi_high_half (i j : Fin 3) (p : Pphys) (u : Hi) :
    IH ((NH i j p) u) = (NL i j p) (IH u) := by
  have hCoeff : coefficientValue 3 (NJ3 i j p) = coefficientValue 2 (NJ2 i j p) := by
    unfold referenceJacobiBoundaryThreeHalfCoefficientFamily
    exact coefficientValue_compactCoefficient 3 _ _ _
  exact congrArg (fun A : Hi →L[ℝ] Half => A u)
    (nativeCoefficientMulL_high_half_compatibility hcalc hF hO hD τ0
      (NJ3 i j p) (NJ2 i j p) hCoeff)

private lemma zeroRow_jacobi_half_negative (i j : Fin 3) (p : Pphys) (v : Half) :
    JL ((NL i j p) v) = (NN i j p) (JL v) :=
  v017_native_half_negative hcalc hF hO hD τ0 (NJ2 i j p) v

theorem zeroCorrectionHigh_inclusion (i : Fin 3) (p : Pphys) (u : Hi) :
    IH (ZH i p u) = ZL i p (IH u) := by
  exact zeroRow_triple_compat IH p.2.2
    (fun _j : Fin 3 => Dr (3/2 : ℝ) p) (fun j => Mh j) (fun j : Fin 3 => NH i j p)
    (fun _j : Fin 3 => Dr (1/2 : ℝ) p) (fun j => Ml j) (fun j : Fin 3 => NL i j p)
    (fun _j z => sphereSobolevInclusionL_radialDriftAdjoint hF hO hD (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (referenceCenterDrift g L p.1 p.2.1) z)
    (fun j z => sphereSobolevInclusionL_linearCoordinateMul hF hO hD (3/2 : ℝ) (1/2 : ℝ) (by norm_num) (EuclideanSpace.single j (1 : ℝ)) z)
    (fun j z => zeroRow_jacobi_high_half g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j p z) u

theorem zeroCorrectionHalf_inclusion (i : Fin 3) (p : Pphys) (v : Half) :
    JL (ZL i p v) = ZN i p (JL v) := by
  exact zeroRow_triple_compat JL p.2.2
    (fun _j : Fin 3 => Dr (1/2 : ℝ) p) (fun j => Ml j) (fun j : Fin 3 => NL i j p)
    (fun _j : Fin 3 => Dr (-(1/2 : ℝ)) p) (fun j => Mn j) (fun j : Fin 3 => NN i j p)
    (fun _j z => sphereSobolevInclusionL_radialDriftAdjoint hF hO hD (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (referenceCenterDrift g L p.1 p.2.1) z)
    (fun j z => sphereSobolevInclusionL_linearCoordinateMul hF hO hD (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num) (EuclideanSpace.single j (1 : ℝ)) z)
    (fun j z => zeroRow_jacobi_half_negative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j p z) v

attribute [local irreducible] referencePiThreeHalfMultiplier referencePiHalfMultiplier
  referencePiNegativeHalfMultiplier sharpRemainder lowerSharpRemainder
  loweringHigh loweringLow sphereSobolevInclusionL sphereSobolevRadialDriftAdjointL
  sphereSobolevLinearCoordinateMulL nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL
  nativeNegativeHalfCoefficientMulL referenceJacobiBoundaryThreeHalfCoefficientFamily
  referenceJacobiBoundaryCoefficientFamily

/-- Exact `J k^h = k^l I` from one current Pi jet and the retained segment. -/
theorem zeroRowReverse_low_compatibility
    (i : Fin 3) (t : Tpar)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (t.1.1,(t.1.2.1,θ*t.1.2.2)) ∈ Ω)
    (Q : SmoothCoefficientJets 3)
    (hPiL : nativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) = PiL i t)
    (hPiN : nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) = PiN i t)
    (u : Hi) : JL (kH i t u) = kL i t (IH u) := by
  have hPi (v : Half) : JL (PiL i t v)=PiN i t (JL v) := by
    rw [← hPiL,← hPiN]
    exact v017_native_half_negative hcalc hF hO hD τ0 (smoothMultiplierLowerJets Q) v
  have hRad (v : Hi) : JL (PiL i t (Sh t.1 v))=PiN i t (Sl t.1 (IH v)) :=
    (hPi (Sh t.1 v)).trans (congrArg (PiN i t)
      (v016_actual_Sh_compat hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData t.1 hSeg v).symm)
  have hAng (j : Fin 3) (v : Hi) : JL ((NL i j t.1) (loweringHigh hF hO hD j v))=
      (NN i j t.1) (loweringLow hF hO hD j (IH v)) :=
    (zeroRow_jacobi_half_negative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j t.1
      (loweringHigh hF hO hD j v)).trans
      (congrArg (NN i j t.1) (v017_inclusion_loweringHigh hF hO hD j v))
  unfold zeroRowReverseHigh zeroRowReverseLow
  exact zeroRow_reversePair_compat IH JL ((PiL i t).comp (Sh t.1)) ((PiN i t).comp (Sl t.1))
    (fun j => (NL i j t.1).comp (loweringHigh hF hO hD j))
    (fun j => (NN i j t.1).comp (loweringLow hF hO hD j)) hRad hAng u

/-- Exact ordered K/Z graph at one literal current t. -/
theorem zeroCorrectionKHigh_graph (i j : Fin 3) (t : Tpar)
    (hk : ∀ u : Hi, JL (kH i t u) = kL i t (IH u)) (u : Hi) :
    JL (KZh i j t u) = KZl i j t (IH u) := by
  unfold zeroCorrectionKHigh zeroCorrectionKLow
  exact orderedKZ_graph IH JL (kH i t) (kL i t) (ZH j t.1) (ZL j t.1) (ZN j t.1) hk
    (zeroCorrectionHigh_inclusion g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 j t.1)
    (zeroCorrectionHalf_inclusion g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 j t.1) u

/-! ### Ambient smoothness of the three zero-correction words. -/

private lemma zeroCorrection_contDiffAt (t : Tpar)
    (hNH : ∀ i j : Fin 3, ContDiffAt ℝ ∞ (fun z : Tpar => NH i j z.1) t)
    (hNL : ∀ i j : Fin 3, ContDiffAt ℝ ∞ (fun z : Tpar => NL i j z.1) t)
    (hNN : ∀ i j : Fin 3, ContDiffAt ℝ ∞ (fun z : Tpar => NN i j z.1) t) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun z : Tpar => ZH i z.1) t ∧
    ContDiffAt ℝ ∞ (fun z : Tpar => ZL i z.1) t ∧
    ContDiffAt ℝ ∞ (fun z : Tpar => ZN i z.1) t := by
  have hProj : ContDiff ℝ ∞ (fun z : Tpar => (z.1.1,z.1.2.1)) :=
    contDiff_fst.fst.prodMk contDiff_fst.snd.fst
  have hDr (s : ℝ) : ContDiffAt ℝ ∞ (fun z : Tpar => Dr s z.1) t :=
    ((contDiff_reference_sphereSobolevRadialDriftAdjointL g hg L hF hO hD s).comp hProj).contDiffAt
  have hr : ContDiffAt ℝ ∞ (fun z : Tpar => z.1.2.2) t := contDiffAt_fst.snd.snd
  refine ⟨?_,?_,?_⟩
  · exact hr.smul (ContDiffAt.sum (fun j _ => (hDr _).clm_comp (contDiffAt_const.clm_comp (hNH i j))))
  · exact hr.smul (ContDiffAt.sum (fun j _ => (hDr _).clm_comp (contDiffAt_const.clm_comp (hNL i j))))
  · exact hr.smul (ContDiffAt.sum (fun j _ => (hDr _).clm_comp (contDiffAt_const.clm_comp (hNN i j))))

/-! ### Theorem A: any retained witness `W`, every point of the CLOSED room. -/

/-- For ANY coefficient germ room `W` on a segment-admissible common room, the literal
K/Z rows have ambient C^∞ germs at every point of the closed parameter room (boundary
included), exact paired compatibility, and uniform finite mixed jets whose bound
depends only on the requested budget `N` (and the fixed `δ`, `W`). -/
theorem zeroCorrectionK_rows_of_coeffRoom
    (hreg : FixedDirichletRegularity) {δ : ℝ} (hRoom : commonRoom y0 ρ δ ⊆ Ω) (W : CoeffRoom δ) :
    (∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ContDiffAt ℝ ∞ (kH i) t ∧ ContDiffAt ℝ ∞ (kL i) t) ∧
    (∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi, JL (kH i t u) = kL i t (IH u)) ∧
    (∀ i j : Fin 3, ∀ t ∈ ParamRoom δ, ContDiffAt ℝ ∞ (KZh i j) t ∧ ContDiffAt ℝ ∞ (KZl i j) t) ∧
    (∀ i j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi, JL (KZh i j t u) = KZl i j t (IH u)) ∧
    (∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, n ≤ N → ∀ t ∈ ParamRoom δ, ∀ i j : Fin 3,
      ‖iteratedFDeriv ℝ n (kH i) t‖ ≤ M ∧ ‖iteratedFDeriv ℝ n (kL i) t‖ ≤ M ∧
      ‖iteratedFDeriv ℝ n (KZh i j) t‖ ≤ M ∧ ‖iteratedFDeriv ℝ n (KZl i j) t‖ ≤ M) := by
  classical
  have hSeg (t : Tpar) (ht : t ∈ ParamRoom δ) :
      ∀ θ ∈ Icc (0 : ℝ) 1, (t.1.1,(t.1.2.1,θ*t.1.2.2)) ∈ Ω :=
    segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoom t.1 ht.1
  -- Pi: native ambient smoothness transferred through the NEIGHBOURHOOD germ of W.
  have hPiAt (i : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) :
      ContDiffAt ℝ ∞ (PiL i) t ∧ ContDiffAt ℝ ∞ (PiN i) t := by
    have hs := commonSupport_native_contDiffAt hcalc hF hO hD τ0 (W.piScalar i) (W.piSmooth i)
      W.piSupport W.piCompact (W.piZero i) t
    have hgerm := W.piGerm i t ht
    exact ⟨hs.2.1.congr_of_eventuallyEq (hgerm.mono (fun z hz => hz.2.1.symm)),
      hs.2.2.congr_of_eventuallyEq (hgerm.mono (fun z hz => hz.2.2.symm))⟩
  -- Jacobi: the same transfer at p = t.1, then composition with the projection.
  have hNAt (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) :
      ContDiffAt ℝ ∞ (fun z : Tpar => NH i j z.1) t ∧
      ContDiffAt ℝ ∞ (fun z : Tpar => NL i j z.1) t ∧
      ContDiffAt ℝ ∞ (fun z : Tpar => NN i j z.1) t := by
    have hs := commonSupport_native_contDiffAt hcalc hF hO hD τ0 (W.jacobiScalar i j)
      (W.jacobiSmooth i j) (W.jacobiSupport i j) (W.jacobiCompact i j) (W.jacobiZero i j) t.1
    have hgerm := W.jacobiGerm i j t.1 ht.1
    have h1 : ContDiffAt ℝ ∞ (fun z : Pphys => NH i j z) t.1 :=
      hs.1.congr_of_eventuallyEq (hgerm.mono (fun z hz => hz.1.symm))
    have h2 : ContDiffAt ℝ ∞ (fun z : Pphys => NL i j z) t.1 :=
      hs.2.1.congr_of_eventuallyEq (hgerm.mono (fun z hz => hz.2.1.symm))
    have h3 : ContDiffAt ℝ ∞ (fun z : Pphys => NN i j z) t.1 :=
      hs.2.2.congr_of_eventuallyEq (hgerm.mono (fun z hz => hz.2.2.symm))
    exact ⟨h1.comp t contDiffAt_fst,h2.comp t contDiffAt_fst,h3.comp t contDiffAt_fst⟩
  -- Sharp radial remainders on the retained invertibility segment.
  have hRemAt (t : Tpar) (ht : t ∈ ParamRoom δ) :
      ContDiffAt ℝ ∞ (fun z : Tpar => Sh z.1) t ∧ ContDiffAt ℝ ∞ (fun z : Tpar => Sl z.1) t := by
    have hRem := contDiffAt_actualAngularRadialRemainder_families_of_segment
      hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hreg t.1 (hSeg t ht)
    exact ⟨hRem.2.2.1.comp (f := fun z : Tpar => z.1) t contDiffAt_fst,
      hRem.2.2.2.comp (f := fun z : Tpar => z.1) t contDiffAt_fst⟩
  have hkAt (i : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) :
      ContDiffAt ℝ ∞ (kH i) t ∧ ContDiffAt ℝ ∞ (kL i) t := by
    obtain ⟨hPL,hPN⟩ := hPiAt i t ht
    obtain ⟨hSh,hSl⟩ := hRemAt t ht
    exact ⟨(hPL.clm_comp hSh).add
        (ContDiffAt.sum (fun j _ => (hNAt i j t ht).2.1.clm_comp contDiffAt_const)),
      (hPN.clm_comp hSl).add
        (ContDiffAt.sum (fun j _ => (hNAt i j t ht).2.2.clm_comp contDiffAt_const))⟩
  have hZAt (j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) :=
    zeroCorrection_contDiffAt g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 t
      (fun i j => (hNAt i j t ht).1) (fun i j => (hNAt i j t ht).2.1)
      (fun i j => (hNAt i j t ht).2.2) j
  have hKZAt (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) :
      ContDiffAt ℝ ∞ (KZh i j) t ∧ ContDiffAt ℝ ∞ (KZl i j) t := by
    have hk := hkAt i t ht
    have hZ := hZAt j t ht
    exact ⟨(hk.1.clm_comp hZ.1).sub (hZ.2.1.clm_comp hk.1),
      (hk.2.clm_comp hZ.2.1).sub (hZ.2.2.clm_comp hk.2)⟩
  have hkCompat (i : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) (u : Hi) :
      JL (kH i t u) = kL i t (IH u) := by
    have hP := (W.piGerm i t ht).self_of_nhds
    exact zeroRowReverse_low_compatibility g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      i t (hSeg t ht) _ hP.2.1 hP.2.2 u
  refine ⟨hkAt,hkCompat,hKZAt,?_,?_⟩
  · intro i j t ht u
    exact zeroCorrectionKHigh_graph g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      i j t (hkCompat i t ht) u
  · intro N
    have hK : IsCompact (ParamRoom δ) :=
      (isCompact_commonRoom y0 ρ δ).prod (isCompact_closedBall _ _)
    let cap1 := exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt
      (kH) (ParamRoom δ) hK (fun i t ht => (hkAt i t ht).1) N
    let M1 : ℝ := Classical.choose cap1
    have facts1 := Classical.choose_spec cap1
    have hM10 : 0 ≤ M1 := facts1.1
    have hM1 := facts1.2
    let cap2 := exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt
      (kL) (ParamRoom δ) hK (fun i t ht => (hkAt i t ht).2) N
    let M2 : ℝ := Classical.choose cap2
    have facts2 := Classical.choose_spec cap2
    have hM20 : 0 ≤ M2 := facts2.1
    have hM2 := facts2.2
    let cap3 := exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt
      (fun ij : Fin 3 × Fin 3 => KZh ij.1 ij.2) (ParamRoom δ) hK
      (fun ij t ht => (hKZAt ij.1 ij.2 t ht).1) N
    let M3 : ℝ := Classical.choose cap3
    have facts3 := Classical.choose_spec cap3
    have hM30 : 0 ≤ M3 := facts3.1
    have hM3 := facts3.2
    let cap4 := exists_compact_uniform_iteratedFDeriv_bound_finite_of_contDiffAt
      (fun ij : Fin 3 × Fin 3 => KZl ij.1 ij.2) (ParamRoom δ) hK
      (fun ij t ht => (hKZAt ij.1 ij.2 t ht).2) N
    let M4 : ℝ := Classical.choose cap4
    have facts4 := Classical.choose_spec cap4
    have hM40 : 0 ≤ M4 := facts4.1
    have hM4 := facts4.2
    refine ⟨M1+M2+M3+M4,by linarith,?_⟩
    intro n hn t ht i j
    exact ⟨(hM1 n hn t ht i).trans (by linarith),
      (hM2 n hn t ht i).trans (by linarith),
      (hM3 n hn t ht (i,j)).trans (by linarith),
      (hM4 n hn t ht (i,j)).trans (by linarith)⟩

attribute [local irreducible] canonicalHigh canonicalLow zeroReverseEHigh zeroReverseELow

/-! ### Theorem B: the actual W obtained ONCE, both complete zero rows on it. -/

/-- One actual `(δ, W)` from the ordinary endpoint producer. On that same witness:
canonical endpoints, the native z/E zero row and the literal K/Z zero row, each with
ambient C^∞ germs at every point of the closed parameter room, exact paired
inclusion compatibility, and one uniform finite mixed-jet bound per budget `N`.
`δ, W` precede `N`; `M` precedes `n, t, i, j`; no profile/cutoff/input enters. -/
theorem exists_commonRoom_actual_fullE_zero_rows_smooth_germs
    (hreg : FixedDirichletRegularity) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ commonRoom y0 ρ δ ⊆ Ω ∧
    ∃ W : CoeffRoom δ,
      (∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ContDiffAt ℝ ∞ (EH i) t ∧ ContDiffAt ℝ ∞ (EL i) t) ∧
      (∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi, JL (EH i t u) = EL i t (IH u)) ∧
      (∀ i j : Fin 3, ∀ t ∈ ParamRoom δ,
        ContDiffAt ℝ ∞ (zEh i j) t ∧ ContDiffAt ℝ ∞ (zEl i j) t) ∧
      (∀ i j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi, JL (zEh i j t u) = zEl i j t (IH u)) ∧
      (∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ContDiffAt ℝ ∞ (kH i) t ∧ ContDiffAt ℝ ∞ (kL i) t) ∧
      (∀ i : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi, JL (kH i t u) = kL i t (IH u)) ∧
      (∀ i j : Fin 3, ∀ t ∈ ParamRoom δ,
        ContDiffAt ℝ ∞ (KZh i j) t ∧ ContDiffAt ℝ ∞ (KZl i j) t) ∧
      (∀ i j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi, JL (KZh i j t u) = KZl i j t (IH u)) ∧
      (∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ, n ≤ N → ∀ t ∈ ParamRoom δ, ∀ i j : Fin 3,
        ‖iteratedFDeriv ℝ n (EH i) t‖ ≤ M ∧ ‖iteratedFDeriv ℝ n (EL i) t‖ ≤ M ∧
        ‖iteratedFDeriv ℝ n (kH i) t‖ ≤ M ∧ ‖iteratedFDeriv ℝ n (kL i) t‖ ≤ M ∧
        ‖iteratedFDeriv ℝ n (zEh i j) t‖ ≤ M ∧ ‖iteratedFDeriv ℝ n (zEl i j) t‖ ≤ M ∧
        ‖iteratedFDeriv ℝ n (KZh i j) t‖ ≤ M ∧ ‖iteratedFDeriv ℝ n (KZl i j) t‖ ≤ M) := by
  let ordinaryWitnesses := exists_commonRoom_actual_fullE_ordinary_endpoints
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg
  let δ : ℝ := Classical.choose ordinaryWitnesses
  have ordinaryFacts := Classical.choose_spec ordinaryWitnesses
  have hδ : 0 < δ := ordinaryFacts.1
  have hδρ : δ ≤ ρ := ordinaryFacts.2.1
  have hRoom : commonRoom y0 ρ δ ⊆ Ω := ordinaryFacts.2.2.1
  let W : CoeffRoom δ := Classical.choose ordinaryFacts.2.2.2
  have ordinaryFields := Classical.choose_spec ordinaryFacts.2.2.2
  have hAt := ordinaryFields.1
  have hCompat := ordinaryFields.2.1
  have hGainAt := ordinaryFields.2.2.2.1
  have hGainCompat := ordinaryFields.2.2.2.2.1
  have hCaps := ordinaryFields.2.2.2.2.2
  have zeroFacts := zeroCorrectionK_rows_of_coeffRoom
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hRoom W
  have hkAt := zeroFacts.1
  have hkCompat := zeroFacts.2.1
  have hKZAt := zeroFacts.2.2.1
  have hKZCompat := zeroFacts.2.2.2.1
  have hKZCaps := zeroFacts.2.2.2.2
  refine ⟨δ,hδ,hδρ,hRoom,W,fun i t ht => ⟨(hAt i t ht).1,(hAt i t ht).2.1⟩,
    fun i t ht u => (hCompat i t ht u).1,hGainAt,hGainCompat,hkAt,hkCompat,hKZAt,hKZCompat,?_⟩
  intro N
  let ordinaryCaps := hCaps N
  let M0 : ℝ := Classical.choose ordinaryCaps
  have ordinaryCapFacts := Classical.choose_spec ordinaryCaps
  have hM00 : 0 ≤ M0 := ordinaryCapFacts.1
  have hM0 := ordinaryCapFacts.2
  let zeroCaps := hKZCaps N
  let M1 : ℝ := Classical.choose zeroCaps
  have zeroCapFacts := Classical.choose_spec zeroCaps
  have hM10 : 0 ≤ M1 := zeroCapFacts.1
  have hM1 := zeroCapFacts.2
  refine ⟨M0+M1,by linarith,?_⟩
  intro n hn t ht i j
  have h0 := hM0 n hn t ht i
  have h0j := h0.2.2.2.2 j
  have h1 := hM1 n hn t ht i j
  exact ⟨h0.1.trans (by linarith),h0.2.1.trans (by linarith),
    h1.1.trans (by linarith),h1.2.1.trans (by linarith),
    h0j.1.trans (by linarith),h0j.2.trans (by linarith),
    h1.2.2.1.trans (by linarith),h1.2.2.2.trans (by linarith)⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEZeroRowsSmoothGerms

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEZeroRowsSmoothGerms.zeroCorrectionK_rows_of_coeffRoom
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEZeroRowsSmoothGerms.exists_commonRoom_actual_fullE_zero_rows_smooth_germs
