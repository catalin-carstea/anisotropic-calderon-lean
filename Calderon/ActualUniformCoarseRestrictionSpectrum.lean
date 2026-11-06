import Calderon.ActualUniformNativeSpectrumPowerBound
import MixedKernelCurrentCrossSeries
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Regularity.classicalHarmonicL2Space harmonicRestrict

theorem exists_uniform_coarse_harmonicRestrict_spectrum_power_bound
    (S : KnownSideSourceData) (B s0 s1 α β : ℝ)
    (hB : 0 < B) (hs0 : 0 < s0) (hss : s0 ≤ s1) (hα : 0 < α) (hα4 : α ≤ 1/4) (hβ : 0 < β) :
    ∃ lambda0 : ℝ, 0 < lambda0 ∧ lambda0 ≤ 1 ∧ ∃ P : ℝ, 1 ≤ P ∧
      ∀ lambda ∈ Icc (0:ℝ) lambda0, ∀ p : R3, ‖p‖ ≤ B → ∀ s ∈ Icc s0 s1,
      let eta := s/20
      let c := p-eta • EuclideanSpace.single (2:Fin 3) (1:ℝ)
      let D := ball c (3*eta)
      let T := ball c ((1-α/2)*eta)
      ∀ hTD : T ⊆ D, ∀ (ι : Type)
      (w : ι → harmonicSub D isOpen_ball (dilatedFirstPrincipal S lambda)
        (contDiff_dilatedFirstPrincipal S lambda).contDiffOn), Orthonormal ℝ w →
      ∀ μ : ι → ℝ, (∀ j, 0 < μ j) → (∀ j, μ j ≤ 1) →
      (∀ j l, inner ℝ (harmonicRestrict D isOpen_ball (dilatedFirstPrincipal S lambda)
        (contDiff_dilatedFirstPrincipal S lambda).contDiffOn T hTD (w j))
        (harmonicRestrict D isOpen_ball (dilatedFirstPrincipal S lambda)
        (contDiff_dilatedFirstPrincipal S lambda).contDiffOn T hTD (w l)) = if j=l then μ j^2 else 0) →
      (∑' j, μ j^β) ≤ P := by
  let gs : Fin 2 → MatrixField := ![S.g1,S.g2]
  have hgs : ∀ i : Fin 2, IsAdmissibleMetric (gs i) := by
    intro i
    fin_cases i
    · exact S.g1_admissible
    · exact S.g2_admissible
  have hs1 : 0 < s1 := hs0.trans_le hss
  let Bbig := B+5*s1+1
  have hBbig : 0 < Bbig := by dsimp [Bbig];linarith
  let d := s0/80
  have hd : 0 < d := by dsimp [d];positivity
  obtain ⟨lambda0,hlambda0,hlambda01,hRoom,hPower⟩ :=
    exists_uniform_native_harmonicRestrict_spectrum_power_bound gs hgs Bbig hBbig 1 (by norm_num)
  obtain ⟨P,hP,hPoint⟩ := hPower 0 β hβ d hd
  refine ⟨lambda0,hlambda0,hlambda01,P,hP,?_⟩
  intro lambda hlambda p hp s hs eta c D T hTD ι w hw μ hμ hμ1 hgram
  have heta : 0 < eta := by dsimp [eta];linarith [hs.1]
  have hrT : 0 < (1-α/2)*eta := mul_pos (by linarith) heta
  have he2 : ‖EuclideanSpace.single (2:Fin 3) (1:ℝ)‖ = 1 := by simp
  have hc : ‖c‖ ≤ B+eta := by
    have h := norm_sub_le p (eta • EuclideanSpace.single (2:Fin 3) (1:ℝ))
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos heta,he2,mul_one] at h
    exact h.trans (by linarith only [hp])
  have hD : D ⊆ ball (0:R3) Bbig := by
    intro x hx
    have hxC : ‖x-c‖ < 3*eta := by
      change dist x c < 3*eta at hx
      simpa only [dist_eq_norm] using hx
    have hxN := norm_add_le (x-c) c
    rw [sub_add_cancel] at hxN
    rw [mem_ball,dist_zero_right]
    dsimp [Bbig]
    have hetaUpper : eta ≤ s1/20 := by dsimp [eta];linarith [hs.2]
    linarith
  have hClosure : closure T ⊆ closedBall c ((1-α/2)*eta) :=
    closure_minimal ball_subset_closedBall isClosed_closedBall
  have hTcompact : IsCompact (closure T) :=
    (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hClosure
  have hTne : T.Nonempty := nonempty_ball.mpr hrT
  have hBuffer : ∀ x ∈ closure T, closedBall x (2*d) ⊆ D := by
    intro x hx z hz
    have hxC := mem_closedBall.mp (hClosure hx)
    have hzX := mem_closedBall.mp hz
    have hDist := dist_triangle z x c
    apply mem_ball.mpr
    have hEtaLower : s0/20 ≤ eta := by dsimp [eta];linarith [hs.1]
    have hAlphaEta : 0 < α*eta := mul_pos hα heta
    dsimp [d] at *
    nlinarith only [hxC,hzX,hDist,hEtaLower,hAlphaEta,heta,hs0]
  have hResult := hPoint lambda hlambda D isOpen_ball hD T isOpen_ball hTne hTcompact hBuffer hTD ι w hw μ hμ hμ1 hgram
  exact hResult

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
