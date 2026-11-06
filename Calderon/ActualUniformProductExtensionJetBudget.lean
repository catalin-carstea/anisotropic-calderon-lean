import Calderon.ActualUniformCurrentCommonPair
import Calderon.ActualUniformFixedRoomRestrictionSpectrum
import Calderon.ActualBoundedProductL2Budget
import Calderon.ActualCurrentCoefficientProductNormBounds
import Calderon.ActualUniformCurrentCrossKernelJets
import MixedKernelHessianExtensionConstruction
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
attribute [local instance] Classical.propDecidable
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap
open ExteriorSource ConnectionError MetricOperator MetricVolume
open ActualNormalizedSecondMetricDrift NormalizedPrincipalMetric
open CoordinateBootstrapJets ActualHigherRadiusProfile ConformalDepth ReferenceWeightedApproximation
open Geometry

theorem exists_uniform_product_extension_with_compact_cross_jet_budget
    (S:KnownSideSourceData) (p1 p2:R3) (U:Set (R3×R3)) (hU:IsOpen U) (hpU:(p1,p2)∈U)
    (rho:R3×R3→ℝ) (hrho:ContDiffOn ℝ ∞ rho U) (hrho0:rho (p1,p2)=0)
    (hTest:ProductHessianStrictAt (fun x => S.g1 ((0:ℝ) • x))
      (fun y => S.g2 ((0:ℝ) • y)) p1 p2 rho) :
    ∃ lambda0 r:ℝ,0 < lambda0 ∧ 0 < r ∧ ∃ Ksource V:Set (R3×R3),
      IsCompact Ksource ∧ Ksource⊆{z | z∈U ∧ 0 < rho z} ∧
      IsOpen V ∧ (p1,p2)∈V ∧ V⊆U ∧ ball (p1,p2) r⊆V ∧
      ∃ C:ℕ→ℝ,(∀ n,0 < C n) ∧
      ∀ L:ℝ,∀ lambda∈Icc (0:ℝ) lambda0,∀ F:R3×R3→ℝ,
      ProductSolutionOn S L lambda F {z | z∈U ∧ 0 < rho z} →
      ∀ M:ℝ,0 ≤ M → (∀ z∈Ksource,‖F z‖ ≤ M) →
      ∃ G:R3×R3→ℝ,ProductSolutionOn S L lambda G V ∧
        EqOn G F (V∩{z | z∈U ∧ 0 < rho z}) ∧
        ∀ n:ℕ,∀ z∈ball (p1,p2) r,‖iteratedFDeriv ℝ n G z‖ ≤ C n*M := by
  obtain ⟨lamRoom,hlamRoom,D1,hD1,O1,hO1D1,T,hTD1,D2,O2,S2,K1i,K2i,gamma1,gamma2,
    hfacts,hO1conn,hO2conn,hO1T,hO2S,
    ⟨ell2,e2,l,eps,R,heps,hl,hR,hO2def,hS2def,hDt,hmonotone⟩,H⟩ :=
    uniform_near_dilation_current_common_pair_from_product_hessian_monotone S 0 p1 p2 U hU hpU rho hrho hrho0 hTest
  rcases hfacts with ⟨hD1o,hD1c,hO1,hp1,hOD1,hT,hTne,hTD,
    hD2,hD2c,hO2,hp2,hOD2,hS2,hS2ne,hSD2,
    hK1i,hK2i,hgamma11,hgamma12,hgamma21,hgamma22,
    K1,KT,J2,JS,eta,hK1,hKT,hJ2,hJS,hD1K1,hTKT,hKTD1,hD2J2,hS2JS,hJSD2,hKU,heta,hmargin⟩
  let Omega:Set (R3×R3) := {z | z∈U ∧ 0 < rho z}
  have hOmega:IsOpen Omega := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    exact Filter.inter_mem (hU.mem_nhds hz.1)
      ((hrho.contDiffAt (hU.mem_nhds hz.1)).continuousAt.preimage_mem_nhds (Ioi_mem_nhds hz.2))
  have hrow:KT×ˢJ2⊆Omega := fun z hz =>
    ⟨hKU ⟨hD1K1 (hKTD1 hz.1),hz.2⟩,heta.trans_le (hmargin z (Or.inr hz))⟩
  have hobs:K1×ˢJS⊆Omega := fun z hz =>
    ⟨hKU ⟨hz.1,hD2J2 (hJSD2 hz.2)⟩,heta.trans_le (hmargin z (Or.inl hz))⟩
  let Ksource:Set (R3×R3) := K1×ˢJS ∪ KT×ˢJ2
  have hKsource:IsCompact Ksource := (hK1.prod hJS).union (hKT.prod hJ2)
  have hKsourceOmega:Ksource⊆Omega := Set.union_subset hobs hrow
  obtain ⟨B0,hB0⟩ := (hK1.union hJ2).exists_bound_of_continuousOn (continuous_id:Continuous (fun x:R3 => x)).continuousOn
  let B:ℝ := max B0 1+1
  have hB:0 < B := by dsimp only [B];positivity
  have hBclosed:K1∪J2⊆closedBall (0:R3) B := by
    intro x hx
    rw [mem_closedBall_zero_iff]
    exact (hB0 x hx).trans (by dsimp only [B];linarith only [le_max_left B0 1])
  have hO1B:O1⊆ball (0:R3) B := by
    intro x hx
    rw [mem_ball,dist_zero_right]
    exact (hB0 x (Or.inl (hD1K1 (hO1D1 hx)))).trans_lt (by dsimp only [B];linarith only [le_max_left B0 1])
  have hO2B:O2⊆ball (0:R3) B := by
    intro x hx
    rw [mem_ball,dist_zero_right]
    exact (hB0 x (Or.inr (hD2J2 (hOD2 hx)))).trans_lt (by dsimp only [B];linarith only [le_max_left B0 1])
  have hTB:T⊆closedBall (0:R3) B := fun x hx => hBclosed (Or.inl (hD1K1 (hTD1 hx)))
  have hD1B:D1⊆closedBall (0:R3) B := fun x hx => hBclosed (Or.inl (hD1K1 hx))
  have hD2B:D2⊆closedBall (0:R3) B := fun x hx => hBclosed (Or.inr (hD2J2 hx))
  have hS2B:S2⊆closedBall (0:R3) B := fun x hx => hBclosed (Or.inr (hD2J2 (hSD2 hx)))
  obtain ⟨Cvol,hCvol,Hvol⟩ := exists_bounded_product_L2_norm_budget B
  have hgamma:0 < gamma1+gamma2-1 := by linarith
  obtain ⟨lamP,P,hlamP,hlamP1,hP,HP⟩ := exists_uniform_fixed_room_harmonicRestrict_spectrum_power_bound
    S D1 K1 T KT hD1 hK1 hD1K1 hT hTne hKT hTKT hKTD1 (gamma1+gamma2-1) hgamma
  obtain ⟨lamJ,hlamJ,hlamJ1,HJet⟩ := exists_uniform_currentCrossKernel_buffered_jet_bound S B hB
  obtain ⟨eps1,heps1,hBall1⟩ := Metric.isOpen_iff.mp hO1 p1 hp1
  obtain ⟨eps2,heps2,hBall2⟩ := Metric.isOpen_iff.mp hO2 p2 hp2
  let r:ℝ := min eps1 eps2/4
  have hr:0 < r := div_pos (lt_min heps1 heps2) (by norm_num)
  have h2r1:2*r < eps1 := by dsimp only [r];linarith only [min_le_left eps1 eps2,lt_min heps1 heps2]
  have h2r2:2*r < eps2 := by dsimp only [r];linarith only [min_le_right eps1 eps2,lt_min heps1 heps2]
  have hBuf1:∀ z∈ball (p1,p2) r,closedBall z.1 r⊆O1 := by
    intro z hz x hx
    have hz1:dist z.1 p1 < r := (max_lt_iff.mp (show max (dist z.1 p1) (dist z.2 p2)<r from hz)).1
    apply hBall1
    apply mem_ball.mpr
    exact (dist_triangle x z.1 p1).trans_lt (by linarith only [mem_closedBall.mp hx,hz1,h2r1])
  have hBuf2:∀ z∈ball (p1,p2) r,closedBall z.2 r⊆O2 := by
    intro z hz x hx
    have hz2:dist z.2 p2 < r := (max_lt_iff.mp (show max (dist z.1 p1) (dist z.2 p2)<r from hz)).2
    apply hBall2
    apply mem_ball.mpr
    exact (dist_triangle x z.2 p2).trans_lt (by linarith only [mem_closedBall.mp hx,hz2,h2r2])
  choose CJ hCJ HCJ using fun n:ℕ => HJet n r hr
  let C:ℕ→ℝ := fun n => CJ n*K1i*|K2i| *Cvol*P+1
  have hPpos:0 < P := zero_lt_one.trans_le hP
  let lambda0:ℝ := min lamRoom (min lamP lamJ)
  have hlambda0:0 < lambda0 := lt_min hlamRoom (lt_min hlamP hlamJ)
  have hboxU:O1×ˢO2⊆U := fun z hz => hKU ⟨hD1K1 (hO1D1 hz.1),hD2J2 (hOD2 hz.2)⟩
  refine ⟨lambda0,r,hlambda0,hr,Ksource,O1×ˢO2,hKsource,hKsourceOmega,hO1.prod hO2,
    ⟨hp1,hp2⟩,hboxU,(fun z hz => ⟨hBuf1 z hz (mem_closedBall_self hr.le),hBuf2 z hz (mem_closedBall_self hr.le)⟩),
    C,(fun n => by have hCJn := hCJ n; dsimp only [C];positivity),?_⟩
  intro L lambda hlam F hSol M hM hBound
  have hlamR:lambda∈closedBall (0:ℝ) lamRoom := by
    rw [mem_closedBall,Real.dist_eq,sub_zero,abs_of_nonneg hlam.1]
    exact hlam.2.trans (min_le_left _ _)
  have hlamP':lambda∈Icc (0:ℝ) lamP := ⟨hlam.1,hlam.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hlamJ':lambda∈Icc (0:ℝ) lamJ := ⟨hlam.1,hlam.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  obtain ⟨HB,HA,HSer⟩ := H L lambda hlamR
  obtain ⟨iota,w,mu,hser⟩ := HSer F hSol
  have hFrow:=productCurrent_memLp_product Omega F hSol.1 T D2 KT J2 hT hD2 hKT hJ2 hTKT hD2J2 hrow
  have hFobs:=productCurrent_memLp_product Omega F hSol.1 D1 S2 K1 JS hD1 hS2 hK1 hJS hD1K1 hS2JS hobs
  have hRowNorm:=Hvol T D2 hT.measurableSet hD2.measurableSet hTB hD2B F hFrow M hM
    (fun z hz => hBound z (Or.inr ⟨hTKT hz.1,hD2J2 hz.2⟩))
  have hObsNorm:=Hvol D1 S2 hD1.measurableSet hS2.measurableSet hD1B hS2B F hFobs M hM
    (fun z hz => hBound z (Or.inl ⟨hD1K1 hz.1,hS2JS hz.2⟩))
  have harms:=currentCoefficient_arms_of_productL2_bounds S L lambda Omega hOmega F hSol
    D1 K1 T KT D2 J2 S2 JS hD1 hK1 hD1K1 hT hKT hTKT hTD1 hD2 hJ2 hD2J2 hS2 hJS hS2JS
    hrow hobs hFrow hFobs (Cvol*M) (mul_nonneg hCvol.le hM) hRowNorm hObsNorm iota w mu hser.1
  have hTensor:=currentCrossTensorOn_of_arms F S L lambda D1 hD1 O1 hO1D1 T hTD1 D2 O2 S2 hOD2
    hK1i (mul_nonneg hCvol.le hM) hgamma11 hgamma21 HA HB w mu hser.1 hser.2.2.1 harms
  have hPower:=HP lambda hlamP' hTD1 iota w w.orthonormal mu hser.1.1 hser.2.1 hser.1.2.2
  obtain ⟨Mold,g,t,hMold,hae,hg,hmono,ht,hSum,hlim,hfin⟩ :=
    currentCrossSeries_actual_limit F S L lambda D1 hD1 O1 hO1D1 T hTD1
      D2 O2 S2 w mu hser
  let G := currentCrossKernel F S lambda D1 hD1 O1 hO1 hO1D1 T hTD1 w mu
  have hprod : ProductSolutionOn S L lambda G (O1 ×ˢ O2) :=
    currentCrossKernel_productSolutionOn F S L lambda D1 hD1 O1 hO1 hO1D1 T hTD1
      D2 O2 S2 hO2 hOD2 w mu hser t ht
  have hobs : K1 ×ˢ S2 ⊆ {z | z ∈ U ∧ 0 < rho z} := by
    intro z hz
    exact ⟨hKU ⟨hz.1,hD2J2 (hJSD2 (hS2JS hz.2))⟩,
      heta.trans_le (hmargin z (Or.inl ⟨hz.1,hS2JS hz.2⟩))⟩
  have hfirst : EqOn G F (O1 ×ˢ S2) :=
    currentCrossKernel_first_eqOn F S L lambda _ hSol D1 hD1 K1 hK1 hD1K1
      O1 hO1 hO1D1 T hTD1 S2 hobs w mu hser.1
  have hknown : O1 ×ˢ S2 ⊆ {z | z ∈ U ∧ 0 < rho z} :=
    fun z hz => hobs ⟨hD1K1 (hO1D1 hz.1),hz.2⟩
  have heq := eqOn_positive_chart_box_of_monotone S L lambda e2 l eps R heps hl hR hDt
    O1 O2 S2 hO1 hO2 hS2 hO2def hS2def U hU rho hrho.continuousOn hboxU hknown
    hmonotone F G hSol hprod hfirst
  refine ⟨G,hprod,heq,?_⟩
  intro n z hz
  have hjet:=HCJ n lambda hlamJ' F L D1 hD1 O1 hO1 hO1D1 T hTD1 D2 O2 S2 hO2 hOD2
    hO1B hO2B K1i K2i gamma1 gamma2 (Cvol*M) P hK1i.le (mul_nonneg hCvol.le hM)
    iota w mu hser hTensor hPower z (hBuf1 z hz) (hBuf2 z hz)
  change ‖iteratedFDeriv ℝ n G z‖ ≤ _ at hjet
  refine hjet.trans ?_
  dsimp only [C]
  nlinarith only [hM]

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
