import Calderon.ClassicalHarmonicRestrictionFiniteRank
import C3Spectral
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge
attribute [local irreducible] Regularity.classicalHarmonicL2Space harmonicRestrict

theorem exists_uniform_native_harmonicRestrict_finiteRank_approximation
    (g : Fin 2 → MatrixField) (hg : ∀ i : Fin 2, IsAdmissibleMetric (g i))
    (B : ℝ) (hB : 0 < B) (r_ext : ℝ) (hr_ext : 0 < r_ext) :
    ∃ lambda0 : ℝ, 0 < lambda0 ∧ lambda0 ≤ 1 ∧ lambda0*B < min r_ext (5/4:ℝ) ∧
      ∀ (i : Fin 2) (k : ℕ), 1 ≤ k → ∀ d : ℝ, 0 < d →
      ∃ N : ℕ, ∃ Cerror : ℝ, 0 < Cerror ∧
      ∀ lambda ∈ Icc (0:ℝ) lambda0, ∀ (D : Set R3) (hD : IsOpen D), D ⊆ ball (0:R3) B →
      let A : MatrixField := principalCoefficient (fun y : R3 => g i (lambda • y))
      let hA : ContDiffOn ℝ ∞ A D := ((contDiff_principalCoefficient (g i) (hg i)).comp
        (contDiff_const_smul lambda)).contDiffOn
      ∀ (S : Set R3) (hS : IsOpen S), S.Nonempty → IsCompact (closure S) →
      (∀ x ∈ closure S, closedBall x (2*d) ⊆ D) → ∀ hSD : S ⊆ D,
      ∀ n : ℕ, 1 ≤ n → ∃ T : harmonicSub D hD A hA →L[ℝ] Lp ℝ 2 ((volume:Measure R3).restrict S),
        FiniteDimensional ℝ (LinearMap.range T.toLinearMap) ∧
        Module.finrank ℝ (LinearMap.range T.toLinearMap) ≤ N*n^3 ∧
        ‖harmonicRestrict D hD A hA S hSD-T‖ ≤ Cerror/((n:ℝ)^k) := by
  obtain ⟨lambda0,hlambda0,hlambda01,hRoom,hJets,hRank⟩ :=
    Regularity.exists_uniform_dilated_metric_harmonic_compact_jets_and_finite_rank_restriction
      g hg B hB r_ext hr_ext
  refine ⟨lambda0,hlambda0,hlambda01,hRoom,?_⟩
  intro i k hk d hd
  obtain ⟨JH,hJH,CT,hCT,hCE,hApprox⟩ := hRank i k hk d hd
  let J_k : ℝ := max (JH ⟨k,Nat.lt_succ_self k⟩) ((Nat.factorial k:ℝ)*CT)
  let n0 : ℕ := 1+Nat.ceil (2*Real.sqrt 3/d)
  let G_B : ℕ := Nat.ceil ((2*B+4)^3)
  let M_k : ℕ := ∑ j ∈ Finset.range k, 3^j
  let V_B : ℝ := ((volume:Measure R3) (ball (0:R3) B)).toReal
  let Q_k : ℝ := Real.sqrt V_B*J_k*(Real.sqrt 3)^k/(Nat.factorial k:ℝ)
  let Cerror : ℝ := 1+max ((n0:ℝ)^k) Q_k
  have hCerror : 0 < Cerror := hCE
  refine ⟨G_B*M_k,Cerror,hCerror,?_⟩
  intro lambda hlambda D hD hDB A hA S hS hSne hScompact hBuffer hSD n hn
  have hOnD := hApprox lambda hlambda D hD hDB
  have hOnS := hOnD S hS hSne hScompact hBuffer hSD
  let H0 := Regularity.classicalHarmonicL2Space D hD A hA
  let Rc : H0 →L[ℝ] Lp ℝ 2 ((volume:Measure R3).restrict S) :=
    (Lp.LpToLpOfMeasureLeSMul (by simp : (1:ℝ≥0∞) ≠ ⊤)
      (show (volume:Measure R3).restrict S ≤ (1:ℝ≥0∞) • (volume:Measure R3).restrict D from
        by simpa only [one_smul] using Measure.restrict_mono_set volume hSD)).comp H0.toSubmodule.subtypeL
  have hNative : harmonicRestrict D hD A hA S hSD = Rc := by
    delta harmonicRestrict
    exact Eq.refl _
  have hOnN : ∃ T : H0 →L[ℝ] Lp ℝ 2 ((volume:Measure R3).restrict S),
      FiniteDimensional ℝ (LinearMap.range T.toLinearMap) ∧
      Module.finrank ℝ (LinearMap.range T.toLinearMap) ≤ G_B*n^3*M_k ∧
      ‖Rc-T‖ ≤ Cerror/((n:ℝ)^k) ∧ (n<n0 → T=0) := hOnS.2 n hn
  obtain ⟨T,hTfin,hTrank,hTerr,hSmall⟩ := hOnN
  rw [←hNative] at hTerr
  refine ⟨T,hTfin,?_,hTerr⟩
  calc
    Module.finrank ℝ (LinearMap.range T.toLinearMap) ≤ G_B*n^3*M_k := hTrank
    _ = G_B*M_k*n^3 := by ring

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
