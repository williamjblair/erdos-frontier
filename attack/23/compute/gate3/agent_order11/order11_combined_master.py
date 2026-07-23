#!/usr/bin/env python3
"""Reconstructed D11 + k7 + k8 + shipped Gram-atom diagnostic master.

This is a floating cutting-plane diagnostic, not an exact certificate.  Its
purpose is to answer whether full order-11 consistency removes the known
positive-delta pseudo-distributions once the two deterministic rooted-profile
legs and the 87 shipped rank-one moment atoms are restored.

Each profile cache must be either (a) the coloured-extension, orbit-invariant
construction or (b) the stronger full-Aut(R)-averaged construction.  Both
are invariant under relabelling of an unlabeled T9/T10 state.  The statewise
all-one identities are ``sum_R L7_R(H)=e(H)/36`` and
``sum_R L8_R(H)=e(H)/45``.
"""

from __future__ import annotations

import argparse
import json
import math
import pickle
import time
from pathlib import Path

import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix, hstack, vstack

from order11_k8_lift import N10, N11, decode_g6, load_d11, local_maxcut


def load_d10(path: Path) -> csr_matrix:
    data = np.load(path)
    return csr_matrix(
        (data["Dval"], (data["Drow"], data["Dcol"])),
        shape=(1_897, int(data["nJ"])),
    )


def moment_atom_rows(moment_cache: Path, gram_cache: Path) -> list[np.ndarray]:
    states, _, moments = pickle.load(moment_cache.open("rb"))
    if len(states) != 1_897:
        raise AssertionError(len(states))
    by_label = {record[0]: record for record in moments}
    gram = pickle.load(gram_cache.open("rb"))
    rows = []
    for label, vector in zip(gram["atoms_lab"], gram["atoms_vv"]):
        _, _, sigma, _, free_size, integer_matrices = by_label[label]
        root_size = sigma[0]
        falling = math.prod(9 - i for i in range(root_size))
        denominator = falling * math.comb(9 - root_size, free_size) ** 2
        tensor = np.asarray(integer_matrices, dtype=float)
        v = np.asarray(vector, dtype=float)
        row = np.einsum("i,hij,j->h", v, tensor, v) / denominator
        rows.append(row)
    if len(rows) != 87:
        raise AssertionError(len(rows))
    return rows


def normalized_moment_blocks(moment_cache: Path):
    states, _, moments = pickle.load(moment_cache.open("rb"))
    if len(states) != 1_897:
        raise AssertionError(len(states))
    blocks = []
    for label, _, sigma, _, free_size, integer_matrices in moments:
        root_size = sigma[0]
        denominator = math.prod(9 - i for i in range(root_size)) * math.comb(
            9 - root_size, free_size
        ) ** 2
        blocks.append(
            (
                label,
                np.asarray(integer_matrices, dtype=float) / denominator,
            )
        )
    return blocks


class ProfileLeg:
    def __init__(self, cache: Path, marginal_to_r: csr_matrix, denominator: int, u_offset: int):
        data = np.load(cache)
        self.entry_j = data["entry_j"].astype(np.int32)
        self.rid = data["rid"].astype(np.int32)
        self.pa = data["pa"].astype(np.int32)
        self.pb = data["pb"].astype(np.int32)
        self.profile_count = data["profile_count"].astype(np.int32)
        self.nroot = len(self.profile_count)
        self.nstate = marginal_to_r.shape[0]
        self.to_r = marginal_to_r.tocsr()
        self.to_r_transpose = marginal_to_r.T.tocsr()
        self.denominator = denominator
        if "entry_count" in data and "aut_size" in data:
            self.cache_kind = "aut-averaged"
            entry_count = data["entry_count"].astype(float)
            aut_size = data["aut_size"].astype(float)
            self.entry_factor = entry_count / (self.denominator * aut_size[self.rid])
        elif "state_order" in data and "lines" in data:
            self.cache_kind = "orbit-invariant"
            self.entry_factor = np.ones(len(self.entry_j)) / self.denominator
        else:
            raise ValueError(f"{cache} is neither an orbit nor Aut-averaged sound cache")
        self.u_offset = u_offset
        self.masks = [np.flatnonzero(self.rid == root) for root in range(self.nroot)]

    def coloring(self, q: np.ndarray, root: int, seed: int) -> np.ndarray:
        entries = self.masks[root]
        a = self.pa[entries]
        b = self.pb[entries]
        small, large = np.minimum(a, b), np.maximum(a, b)
        count = int(self.profile_count[root])
        key = small.astype(np.int64) * count + large
        unique, inverse = np.unique(key, return_inverse=True)
        weight = np.bincount(
            inverse,
            weights=q[self.entry_j[entries]] * self.entry_factor[entries],
        )
        left, right = unique // count, unique % count
        return local_maxcut(count, left, right, weight, seed=seed, starts=16)

    def landing(self, q: np.ndarray, root: int, color: np.ndarray) -> float:
        entries = self.masks[root]
        same = color[self.pa[entries]] == color[self.pb[entries]]
        selected = entries[same]
        return float(np.sum(q[self.entry_j[selected]] * self.entry_factor[selected]))

    def row(self, nv: int, root: int, color: np.ndarray) -> csr_matrix:
        entries = self.masks[root]
        same = color[self.pa[entries]] == color[self.pb[entries]]
        selected = entries[same]
        coefficient_q = np.bincount(
            self.entry_j[selected],
            weights=self.entry_factor[selected],
            minlength=self.nstate,
        )
        coefficient_r = np.asarray(self.to_r_transpose @ coefficient_q).ravel()
        nonzero = np.flatnonzero(coefficient_r)
        columns = np.concatenate([nonzero, [self.u_offset + root]])
        values = np.concatenate([-coefficient_r[nonzero], [1.0]])
        return csr_matrix(
            (values, (np.zeros(len(columns), dtype=int), columns)), shape=(1, nv)
        )

    def rows(self, nv: int, colors: list[np.ndarray]) -> csr_matrix:
        """Batch-compose one colouring row per root with the marginal."""
        if len(colors) != self.nroot:
            raise ValueError((len(colors), self.nroot))
        selected_parts = []
        for root, color in enumerate(colors):
            entries = self.masks[root]
            same = color[self.pa[entries]] == color[self.pb[entries]]
            selected_parts.append(entries[same])
        selected = np.concatenate(selected_parts) if selected_parts else np.zeros(0, dtype=int)
        coefficient_q = csr_matrix(
            (
                self.entry_factor[selected],
                (self.rid[selected], self.entry_j[selected]),
            ),
            shape=(self.nroot, self.nstate),
        )
        coefficient_r = (coefficient_q @ self.to_r).tocsr()
        tail_width = nv - N11
        tail = csr_matrix(
            (
                np.ones(self.nroot),
                (
                    np.arange(self.nroot),
                    self.u_offset - N11 + np.arange(self.nroot),
                ),
            ),
            shape=(self.nroot, tail_width),
        )
        return hstack([-coefficient_r, tail], format="csr")

    def rows_records(
        self, nv: int, records: list[tuple[int, np.ndarray]]
    ) -> csr_matrix:
        """Batch-compose an arbitrary list of (root, colouring) records."""
        row_ids = []
        selected_entries = []
        roots = []
        for row_id, (root, color) in enumerate(records):
            entries = self.masks[root]
            same = color[self.pa[entries]] == color[self.pb[entries]]
            chosen = entries[same]
            row_ids.append(np.full(len(chosen), row_id, dtype=np.int32))
            selected_entries.append(chosen)
            roots.append(root)
        selected = np.concatenate(selected_entries) if selected_entries else np.zeros(0, dtype=int)
        rows = np.concatenate(row_ids) if row_ids else np.zeros(0, dtype=np.int32)
        coefficient_q = csr_matrix(
            (
                self.entry_factor[selected],
                (rows, self.entry_j[selected]),
            ),
            shape=(len(records), self.nstate),
        )
        coefficient_r = (coefficient_q @ self.to_r).tocsr()
        tail = csr_matrix(
            (
                np.ones(len(records)),
                (
                    np.arange(len(records)),
                    self.u_offset - N11 + np.asarray(roots),
                ),
            ),
            shape=(len(records), nv - N11),
        )
        return hstack([-coefficient_r, tail], format="csr")


def run(args) -> dict[str, object]:
    D11, _ = load_d11(args.d11)
    D10 = load_d10(args.d10)
    D9R = (D10 @ D11).tocsr()
    if D9R.shape != (1_897, N11):
        raise AssertionError(D9R.shape)

    n7, n8 = 107, (0 if args.omit_k8 else 410)
    U7, U8, ETA = N11, N11 + n7, N11 + n7 + n8
    nv = ETA + 1
    leg7 = ProfileLeg(args.k7, D9R, 36, U7)
    leg8 = None if args.omit_k8 else ProfileLeg(args.k8, D11, 45, U8)
    if leg7.nroot != n7 or (leg8 is not None and leg8.nroot != n8):
        raise AssertionError((leg7.nroot, None if leg8 is None else leg8.nroot))

    k8_payload = np.load(args.k8)
    lines10 = k8_payload["lines10"].tolist() if "lines10" in k8_payload else k8_payload["lines"].tolist()
    edge10 = np.asarray(
        [sum(x.bit_count() for x in decode_g6(line)) / 90 for line in lines10]
    )
    edge_r = np.asarray(D11.T @ edge10).ravel()

    static_rows = []
    static_b = []
    row = np.zeros(nv)
    row[:N11] = edge_r
    static_rows.append(csr_matrix(row.reshape(1, -1)))
    static_b.append(0.3197)
    static_rows.append(csr_matrix((-row).reshape(1, -1)))
    static_b.append(-0.2486)
    legs_for_static = [(U7, n7)] + ([] if args.omit_k8 else [(U8, n8)])
    for offset, number in legs_for_static:
        row = np.zeros(nv)
        row[offset : offset + number] = -1
        row[ETA] = 1
        static_rows.append(csr_matrix(row.reshape(1, -1)))
        static_b.append(-2 / 25)

    atom_rows = moment_atom_rows(args.moments, args.gram)
    dynamic_blocks = (
        normalized_moment_blocks(args.moments)
        if args.dynamic_moments or args.resume_state
        else []
    )
    moment_min_norm = float("inf")
    for atom in atom_rows:
        coefficient = np.asarray(D9R.T @ atom).ravel()
        moment_min_norm = min(moment_min_norm, float(np.linalg.norm(coefficient)))
        nonzero = np.flatnonzero(coefficient)
        static_rows.append(
            csr_matrix(
                (
                    -coefficient[nonzero],
                    (np.zeros(len(nonzero), dtype=int), nonzero),
                ),
                shape=(1, nv),
            )
        )
        static_b.append(0.0)

    cuts: list[csr_matrix] = []
    cut_meta: list[tuple[int, int, list[int]]] = []
    profile_keys: set[tuple[int, int, tuple[int, ...]]] = set()
    dynamic_moment_meta: list[tuple[str, list[float]]] = []

    def add(leg_number: int, leg: ProfileLeg, root: int, color: np.ndarray):
        key = (leg_number, root, tuple(int(x) for x in color))
        if key in profile_keys:
            return False
        cuts.append(leg.row(nv, root, color))
        cut_meta.append((leg_number, root, color.astype(int).tolist()))
        profile_keys.add(key)
        return True

    def add_batch(leg_number: int, leg: ProfileLeg, colors: list[np.ndarray]):
        matrix = leg.rows(nv, colors)
        # Mandatory semantic gate: a representative batch row must equal the
        # independently constructed old single-row path coefficientwise.
        sample_root = min(3, leg.nroot - 1)
        difference = matrix.getrow(sample_root) - leg.row(nv, sample_root, colors[sample_root])
        if difference.nnz and float(np.max(np.abs(difference.data))) > 1e-14:
            raise AssertionError((leg_number, sample_root, float(np.max(np.abs(difference.data)))))
        cuts.append(matrix)
        for root, color in enumerate(colors):
            record = (leg_number, root, color.astype(int).tolist())
            cut_meta.append(record)
            profile_keys.add((leg_number, root, tuple(record[2])))

    def add_records_batch(
        leg_number: int, leg: ProfileLeg, records: list[tuple[int, np.ndarray]]
    ):
        if not records:
            return
        matrix = leg.rows_records(nv, records)
        sample = min(3, len(records) - 1)
        root, color = records[sample]
        difference = matrix.getrow(sample) - leg.row(nv, root, color)
        if difference.nnz and float(np.max(np.abs(difference.data))) > 1e-14:
            raise AssertionError((leg_number, root, float(np.max(np.abs(difference.data)))))
        cuts.append(matrix)
        for root, color in records:
            record = (leg_number, root, color.astype(int).tolist())
            cut_meta.append(record)
            profile_keys.add((leg_number, root, tuple(record[2])))

    history = []
    start_iteration = 0
    if args.resume_state:
        payload = pickle.load(args.resume_state.open("rb"))
        if "omit_k8" in payload and bool(payload["omit_k8"]) != bool(args.omit_k8):
            raise ValueError("resume-state --omit-k8 mismatch")
        if "k7_kind" in payload and payload["k7_kind"] != leg7.cache_kind:
            raise ValueError("resume-state k7 cache-kind mismatch")
        if leg8 is not None and "k8_kind" in payload and payload["k8_kind"] != leg8.cache_kind:
            raise ValueError("resume-state k8 cache-kind mismatch")
        history = list(payload.get("history", []))
        start_iteration = (int(history[-1]["iteration"]) + 1) if history else 0
        records7 = []
        records8 = []
        for leg_number, root, color_list in payload["cut_meta"]:
            record = (int(root), np.asarray(color_list, dtype=np.int8))
            if int(leg_number) == 7:
                records7.append(record)
            elif leg8 is not None:
                records8.append(record)
            else:
                raise ValueError("resume state contains k8 rows but --omit-k8 was requested")
        add_records_batch(7, leg7, records7)
        if leg8 is not None:
            add_records_batch(8, leg8, records8)
        block_by_label = {label: tensor for label, tensor in dynamic_blocks}
        for label, vector_list in payload.get("dynamic_moment_meta", []):
            tensor = block_by_label[label]
            vector = np.asarray(vector_list, dtype=float)
            row9 = np.einsum("i,hij,j->h", vector, tensor, vector)
            coefficient = np.asarray(D9R.T @ row9).ravel()
            nonzero = np.flatnonzero(coefficient)
            static_rows.append(
                csr_matrix(
                    (
                        -coefficient[nonzero],
                        (np.zeros(len(nonzero), dtype=int), nonzero),
                    ),
                    shape=(1, nv),
                )
            )
            static_b.append(0.0)
            dynamic_moment_meta.append((label, vector.tolist()))
    else:
        # Every u variable needs an initial cap.
        add_batch(
            7,
            leg7,
            [np.zeros(int(leg7.profile_count[root]), dtype=np.int8) for root in range(n7)],
        )
        if leg8 is not None:
            add_batch(
                8,
                leg8,
                [np.zeros(int(leg8.profile_count[root]), dtype=np.int8) for root in range(n8)],
            )

        # Optional frozen-Horn seed.
        if args.seed_horn:
            horn = pickle.load(args.horn.open("rb"))
            q10_horn = np.maximum(np.asarray(horn["x"][:N10], dtype=float), 0)
            q10_horn /= q10_horn.sum()
            q9_horn = np.asarray(D10 @ q10_horn).ravel()
            add_batch(
                7,
                leg7,
                [leg7.coloring(q9_horn, root, seed=10_000 + root) for root in range(n7)],
            )
            if leg8 is not None:
                add_batch(
                    8,
                    leg8,
                    [leg8.coloring(q10_horn, root, seed=20_000 + root) for root in range(n8)],
                )

    objective = np.zeros(nv)
    objective[ETA] = -1
    equality = csr_matrix(
        (np.ones(N11), (np.zeros(N11, dtype=int), np.arange(N11))), shape=(1, nv)
    )
    checkpoint_path = args.state_out or args.resume_state

    def checkpoint(answer):
        if checkpoint_path is None:
            return
        r_checkpoint = np.asarray(answer.x[:N11])
        support = np.flatnonzero(r_checkpoint > 1e-12)
        with checkpoint_path.open("wb") as handle:
            pickle.dump(
                {
                    "version": 2,
                    "history": history,
                    "cut_meta": cut_meta,
                    "dynamic_moment_meta": dynamic_moment_meta,
                    "r_support": support.tolist(),
                    "r_values": r_checkpoint[support].tolist(),
                    "eta": history[-1]["eta"],
                    "k7_kind": leg7.cache_kind,
                    "k8_kind": None if leg8 is None else leg8.cache_kind,
                    "omit_k8": bool(args.omit_k8),
                },
                handle,
                protocol=4,
            )

    final = None
    for iteration in range(start_iteration, start_iteration + args.max_iterations + 1):
        A_ub = vstack(static_rows + cuts, format="csr")
        b_ub = np.concatenate([np.asarray(static_b), np.zeros(len(cut_meta))])
        started = time.time()
        answer = linprog(
            objective,
            A_ub=A_ub,
            b_ub=b_ub,
            A_eq=equality,
            b_eq=[1.0],
            bounds=[(0, None)] * ETA + [(None, None)],
            method=args.method,
        )
        if not answer.success:
            raise RuntimeError(answer.message)
        final = answer
        r = np.asarray(answer.x[:N11])
        q10 = np.asarray(D11 @ r).ravel()
        q9 = np.asarray(D10 @ q10).ravel()
        u7 = np.asarray(answer.x[U7 : U7 + n7])
        u8 = None if leg8 is None else np.asarray(answer.x[U8 : U8 + n8])
        eta = -float(answer.fun)
        added7 = added8 = 0
        worst7 = worst8 = 0.0
        separation_legs = [(7, leg7, q9, u7)]
        if leg8 is not None:
            separation_legs.append((8, leg8, q10, u8))
        for leg_number, leg, q, u in separation_legs:
            for root in range(leg.nroot):
                distinct = {}
                for color_index in range(args.colorings_per_root):
                    color = leg.coloring(
                        q,
                        root,
                        seed=(
                            1_000_000 * iteration
                            + 10_000 * leg_number
                            + 100_000_000 * color_index
                            + root
                        ),
                    )
                    distinct.setdefault(tuple(int(x) for x in color), color)
                for color in distinct.values():
                    landing = leg.landing(q, root, color)
                    violation = float(u[root] - landing)
                    if leg_number == 7:
                        worst7 = max(worst7, violation)
                    else:
                        worst8 = max(worst8, violation)
                    if violation > 1e-9 and add(leg_number, leg, root, color):
                        if leg_number == 7:
                            added7 += 1
                        else:
                            added8 += 1
        added_moment = 0
        min_moment_eigenvalue = 0.0
        for label, tensor in dynamic_blocks:
            matrix = np.tensordot(q9, tensor, axes=(0, 0))
            matrix = 0.5 * (matrix + matrix.T)
            eigenvalues, eigenvectors = np.linalg.eigh(matrix)
            min_moment_eigenvalue = min(min_moment_eigenvalue, float(eigenvalues[0]))
            negative = [i for i, value in enumerate(eigenvalues) if value < -1e-9][:4]
            for index in negative:
                vector = eigenvectors[:, index]
                row9 = np.einsum("i,hij,j->h", vector, tensor, vector)
                coefficient = np.asarray(D9R.T @ row9).ravel()
                nonzero = np.flatnonzero(coefficient)
                static_rows.append(
                    csr_matrix(
                        (
                            -coefficient[nonzero],
                            (np.zeros(len(nonzero), dtype=int), nonzero),
                        ),
                        shape=(1, nv),
                    )
                )
                static_b.append(0.0)
                dynamic_moment_meta.append((label, vector.tolist()))
                added_moment += 1
        leg7_value = float(u7.sum() - 2 / 25)
        leg8_value = None if u8 is None else float(u8.sum() - 2 / 25)
        recomputed = leg7_value if leg8_value is None else min(leg7_value, leg8_value)
        record = {
            "iteration": iteration,
            "eta": eta,
            "leg7_value": leg7_value,
            "leg8_value": leg8_value,
            "eta_recompute_error": abs(eta - recomputed),
            "added7": added7,
            "added8": added8,
            "added_moment": added_moment,
            "min_moment_eigenvalue": min_moment_eigenvalue,
            "worst7": worst7,
            "worst8": worst8,
            "cut_count": len(cut_meta),
            "r_support_1e-10": int((r > 1e-10).sum()),
            "q10_support_1e-10": int((q10 > 1e-10).sum()),
            "edge_density": float(edge10 @ q10),
            "seconds": time.time() - started,
        }
        history.append(record)
        checkpoint(answer)
        print(json.dumps(record, sort_keys=True), flush=True)
        if eta <= 0 or (added7 == 0 and added8 == 0 and added_moment == 0):
            break

    assert final is not None
    checkpoint(final)
    return {
        "verdict": "FLOAT_CLOSURE_CANDIDATE" if history[-1]["eta"] <= 0 else "NOT_CLOSED",
        "history": history,
        "final_eta": history[-1]["eta"],
        "cut_count": len(cut_meta),
        "moment_atom_rows": len(atom_rows),
        "dynamic_moment_rows": len(dynamic_moment_meta),
        "moment_min_composed_norm": moment_min_norm,
        "scope": (
            f"D11 consistency + {leg7.cache_kind} k7 + 87 shipped Gram atom rows"
            if leg8 is None
            else f"D11 consistency + {leg7.cache_kind} k7 + {leg8.cache_kind} k8 + 87 shipped Gram atom rows"
        ),
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--d11", type=Path, required=True)
    parser.add_argument("--d10", type=Path, default=Path("compute23/regen/c5lift_cache.npz"))
    parser.add_argument("--k7", type=Path, required=True)
    parser.add_argument("--k8", type=Path, required=True)
    parser.add_argument("--moments", type=Path, default=Path("compute23/regen/my_moments_n9.pkl"))
    parser.add_argument("--gram", type=Path, default=Path("compute23/src/anc/moment_gram_w.pkl"))
    parser.add_argument("--horn", type=Path, default=Path("compute23/src/anc/horn_dual.pkl"))
    parser.add_argument("--seed-horn", action="store_true")
    parser.add_argument("--omit-k8", action="store_true")
    parser.add_argument("--dynamic-moments", action="store_true")
    parser.add_argument("--colorings-per-root", type=int, choices=(1, 2, 3), default=1)
    parser.add_argument("--max-iterations", type=int, default=20)
    parser.add_argument("--method", choices=("highs", "highs-ds", "highs-ipm"), default="highs-ipm")
    parser.add_argument("--state-out", type=Path)
    parser.add_argument("--resume-state", type=Path)
    args = parser.parse_args()
    print(json.dumps(run(args), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
