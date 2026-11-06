import Calderon.NativeSmoothBallSobolevFamily
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Data.Nat.Choose.Sum
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped Topology ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily
open EnergyBridge

theorem exists_compact_cutoff_composition_finite_joint_jet_bound
    {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (Theta : H×R3 → R3×R3) (hTheta : ContDiff ℝ ∞ Theta)
    (Q : Set H) (hQ : IsCompact Q) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (G : R3×R3→ℝ) (hG : ContDiff ℝ ∞ G) (t : H), t ∈ Q →
      ∀ M : ℝ, 0 ≤ M → (∀ j ≤ k, ∀ z ∈ closedBall (0:R3) 3,
        ‖iteratedFDeriv ℝ j G (Theta (t,z))‖ ≤ M) →
      ∀ j ≤ k, ∀ z:R3, ‖iteratedFDeriv ℝ j
        (fun v:H×R3 => unitBallSmoothCutoff v.2*G (Theta v)) (t,z)‖ ≤ C*M := by
  let chi : H×R3→ℝ := fun v => unitBallSmoothCutoff v.2
  have hchi : ContDiff ℝ ∞ chi := unitBallSmoothCutoff.contDiff.comp contDiff_snd
  let Z : Set (H×R3) := Q ×ˢ closedBall (0:R3) 3
  have hZ : IsCompact Z := hQ.prod (isCompact_closedBall _ _)
  have hBounds : ∀ n : Fin (k+1), ∃ B:ℝ, ∀ v∈Z,
      ‖iteratedFDeriv ℝ n.val Theta v‖ ≤ B ∧ ‖iteratedFDeriv ℝ n.val chi v‖ ≤ B := by
    intro n
    obtain ⟨B,hB⟩ := hZ.exists_bound_of_continuousOn
      (((hTheta.continuous_iteratedFDeriv (m:=n.val) (by exact_mod_cast le_top)).prodMk
        (hchi.continuous_iteratedFDeriv (m:=n.val) (by exact_mod_cast le_top))).continuousOn)
    exact ⟨B,fun v hv => by simpa only [Prod.norm_def,max_le_iff] using hB v hv⟩
  choose BN HN using hBounds
  obtain ⟨B0,hB0⟩ := (Set.finite_range BN).bddAbove
  let B : ℝ := max B0 1
  have hB : 1 ≤ B := le_max_right _ _
  have HB (n:ℕ) (hn:n≤k) (v:H×R3) (hv:v∈Z) :
      ‖iteratedFDeriv ℝ n Theta v‖ ≤ B ∧ ‖iteratedFDeriv ℝ n chi v‖ ≤ B := by
    let i : Fin (k+1) := ⟨n,by omega⟩
    have hh := HN i v hv
    have hBN : BN i ≤ B := (hB0 (Set.mem_range_self i)).trans (le_max_left _ _)
    exact ⟨hh.1.trans hBN,hh.2.trans hBN⟩
  let D : ℝ := B+1
  have hD : 1 ≤ D := by dsimp only [D];linarith
  let A : ℝ := (Nat.factorial k:ℝ)*D^k
  have hA : 0 ≤ A := by dsimp only [A];positivity
  let C : ℝ := (2:ℝ)^k*B*A+1
  have hC : 0 < C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  intro G hG t ht M hM hSource j hj z
  by_cases hz : z ∈ closedBall (0:R3) 3
  · have hp : (t,z) ∈ Z := ⟨ht,hz⟩
    have hComp (n:ℕ) (hn:n≤k) : ‖iteratedFDeriv ℝ n (G ∘ Theta) (t,z)‖ ≤ A*M := by
      have hGeom : ∀ (i : ℕ), 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i Theta (t,z)‖ ≤ D^i := by
        intro i hi hin
        exact ((HB i (hin.trans hn) (t,z) hp).1.trans (by dsimp only [D];linarith)).trans (le_self_pow₀ hD (by omega))
      have h := norm_iteratedFDeriv_comp_le hG hTheta (by exact_mod_cast le_top) (t,z)
        (fun i hi => hSource i (hi.trans hn) z hz) hGeom
      have hFact : (Nat.factorial n:ℝ) ≤ (Nat.factorial k:ℝ) := by exact_mod_cast Nat.factorial_le hn
      have hPow : D^n ≤ D^k := pow_le_pow_right₀ hD hn
      refine h.trans ?_
      dsimp only [A]
      calc
        _ = ((Nat.factorial n:ℝ)*D^n)*M := by ring
        _ ≤ ((Nat.factorial k:ℝ)*D^k)*M := mul_le_mul_of_nonneg_right (mul_le_mul hFact hPow (by positivity) (by positivity)) hM
    have hMul := norm_iteratedFDeriv_mul_le hchi (hG.comp hTheta) (t,z) (n:=j) (by exact_mod_cast le_top)
    have hSum : (∑ i∈Finset.range (j+1), (j.choose i:ℝ)*‖iteratedFDeriv ℝ i chi (t,z)‖*
        ‖iteratedFDeriv ℝ (j-i) (G ∘ Theta) (t,z)‖) ≤ (2:ℝ)^j*B*(A*M) := by
      calc
        _ ≤ ∑ i∈Finset.range (j+1), (j.choose i:ℝ)*B*(A*M) := by
          apply Finset.sum_le_sum
          intro i hi
          have hin : i≤j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          exact mul_le_mul (mul_le_mul_of_nonneg_left (HB i (hin.trans hj) (t,z) hp).2 (Nat.cast_nonneg _))
            (hComp (j-i) ((Nat.sub_le j i).trans hj)) (norm_nonneg _) (by positivity)
        _ = (∑ i∈Finset.range (j+1), (j.choose i:ℝ))*B*(A*M) := by rw [Finset.sum_mul,Finset.sum_mul]
        _ = _ := by rw [show (∑ i∈Finset.range (j+1), (j.choose i:ℝ))=(2:ℝ)^j by exact_mod_cast Nat.sum_range_choose j]
    refine hMul.trans (hSum.trans ?_)
    have hTwo : (2:ℝ)^j ≤ (2:ℝ)^k := pow_le_pow_right₀ (by norm_num) hj
    calc
      _ ≤ (2:ℝ)^k*B*(A*M) := by gcongr
      _ ≤ C*M := by dsimp only [C];nlinarith only [hM]
  · have hOpen : IsOpen {v:H×R3 | v.2 ∉ closedBall (0:R3) 3} := isClosed_closedBall.isOpen_compl.preimage continuous_snd
    have hZero : (fun v:H×R3 => unitBallSmoothCutoff v.2*G (Theta v)) =ᶠ[𝓝 (t,z)] (fun _ => (0:ℝ)) :=
      Filter.eventually_of_mem (hOpen.mem_nhds hz) fun v hv => by
        have hn : 3 ≤ dist v.2 (0:R3) := (not_le.mp (show ¬ dist v.2 (0:R3) ≤ 3 by simpa only [Set.mem_setOf_eq,mem_closedBall] using hv)).le
        change unitBallSmoothCutoff v.2 * G (Theta v) = 0
        rw [unitBallSmoothCutoff.zero_of_le_dist hn,zero_mul]
    rw [(hZero.iteratedFDeriv ℝ j).eq_of_nhds]
    simpa using mul_nonneg hC.le hM

end OAI.AnisotropicCalderon.DirichletFamily
