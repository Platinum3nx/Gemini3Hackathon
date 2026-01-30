import Mathlib.Tactic.SplitIfs
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Linarith
import Aesop

def add_product_id (existing_ids : List Int) (new_id : Int) : List Int :=
  if new_id ∈ existing_ids then existing_ids else existing_ids ++ [new_id]

theorem add_product_id_preserves_nodup (existing_ids : List Int) (new_id : Int) (h : existing_ids.Nodup) :
  (add_product_id existing_ids new_id).Nodup := by
  unfold add_product_id
  split_ifs with h_mem
  case pos =>
    exact h
  case neg =>
    rw [List.nodup_append]
    refine ⟨h, List.nodup_singleton new_id, ?_⟩
    aesop
