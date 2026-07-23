#!/usr/bin/env python3
"""Exact checker for a binary order-11 deletion-marginal separator.

Let S be the embedded set of 1,439 order-10 triangle-free isomorphism
types.  The certificate is the elementary inequality

    q(S) <= 6/11

for every uniform vertex-deletion marginal q = D_11 r.  Its proof is the
finite integer assertion that each order-11 type has at most six of its
eleven vertex deletions in S.  The frozen positive-delta Horn optimizer
violates the inequality.

The optimizer is floating-point diagnostic data, so its mass is reproduced
*exactly as stored*: negative roundoff entries are clipped to zero and every
remaining IEEE-754 value is converted with ``Fraction.from_float`` before
normalization.  No tolerance is used in the separating comparison.
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
import pickle
from fractions import Fraction
from pathlib import Path

import numpy as np
from scipy.sparse import csr_matrix

from order11_k8_lift import N10, N11, canonicalize, geng_lines


S_BITSET_B64 = (
    "AAAAAAAIAQAAgEAAAAAQAAABAhQAoAsAAGGAQAHAmAEAIABgIEAYYgAAABAgDAB4CEAAgIEqoABgAAAABTJMYCEAAAgABAAQBQEgCQAAGgAAwAAAAEAgAQwAEAABABgCJQIQMAgYEAAEAAAiASAAACAAQBAAABSiCMAABkIAAgAYQACAAAAAEgAECAAAJCABQABIDQQAAgBAAIAAIggAEgCESAAAgACCAIAAAkAGAIkXgAAEIKAAACQAQAAABRAkAAiEEDhKAAAAAgAAQEAQAIAAIhAAAAAAAAAgAAIIRUIgAICAqAAIwBAiQAICAAAAQABAAAAAAAY4QQIkAAAoIkrAAAqAggAAgggwAAAACiAIxAATAABgAAAAOQEDAAAIGAAAEAEBwAAgBAAAAATAAAEogAUAJCAAACAAAUUgRBIAgMCBCEAkALiAAAAAQAIBAhmBiBICSAAAAEAAAAJAgAAAIQBACAgAAAAAICAACABUEAIwGACATDAsIKQYFYAEoEAYIIIAAAASAACAEgIAAABBAAAAAEEgAAAgJBAIAAAAABAFAAQAAkgCAEEAAAAAAgALA0GAEAJACAAAAAAAAAABggQAkAAAAAYoCFAAAEAIAAAgACAAAIQQAABAAAAARgKAIAADggIAAAZAIEAAAAADIABAgAQgQAAAACmGAEAEBbAEBAqAAECAgDCBJURABIUFIBAgAgQAIAJAACkAABAIIAQnABQEQEAQBARiAggAAQKCcRIAAIIABXoAAAARAAQABAAAABOAiAAAAghyAAAAAAgIBAAAAEgABAAEIAAAQAAAAAAQCAAAJACQAABkAQIAQAggggAEBJAABAhKAEQEGAAAQEAAAgEUEAEAAEACABAAgBgQAQIAAECBAGAMwgJAAACQAAAAADAAgAIAMhARAAAAAIEJAAQwQgAAAgAUAAQAIIJSAAAAgAAAQBAAAggOAAChACAIAAAAAACABgRAgCEA4AEJBKAICABEAgAAECAKEAIACAADAgQAEIAAACBCwAQAAMAAIUAAAiIAgARwAABAEgaIUgAAAIApAQEAAAVAAAAAsAAAAAUIoBpDABQAgIAAAUMEACDICgAEAAAAAAAAAAAAAAABAAIAAAAEAAAAUAAPGggQAoDZAAAAAAABKIECCBBggUAVTIYkwAASAgCgBAAABAAAAQiCxgiAABAgABgAEICUBAogAIBgEAAAAAAIFQUAEgAATwgBAAAEAAIAAAAAAAAAAAAAAAAAAAAIQKBZAIAAIIECiAAMEAABCAABCAgAAIAAoAIAigKEJAgnAQIEAEwAWAAAAAAAEAAAGQAAAAECQEARYAAIAAAAAGIArCAAhgAAYAhpCAAAAAAAQAAISAYAEMBCYAAABCAABAIIAFICJCACYQACqAAEACiiQYAQgAEZAAQoAAAAAAgDogAIEJYAAAiwoACRQoAEBggQCQAJAgghAAQBAEAISAgUBEaAIQgIAAAAICIAEBgQYAAEAQAKAACkiYgKADAJABgAABgCAAgAQAgAAAgBgAAIAAQCAQIgAiACAAAAiAAABgCAAAAAIAFQABAACAUCABEAAAABAAAAAhAgBAABFgQAAAAAAIABQACAAQAMjABgAAAAAAAQgQBiAhUIAAAgCQASVERHFkAKAEgAEwAAIADQgAAAGMAAACAAAAAAABAwgFCAIAIAABAAREWgCCAgIjgCBgQAAVEAAAAAAwVAQIsEAqAAAgJyAAAAEAABARgYAAgQAAAAAQAAAQAgAAAAIMAAgEgwBAcAIASAAEAABAAAgAAAAAgAAQCACAAAAAAAAIAAIIAAAAEAACAAAJICAQAQEQgAIAhIgQEEjFkAgAgAoAIJABAAAAAADgAAAgAAAAAMAAAAAAAAAABaBAAAIAAAIAAAgAIoIAAAMNKMgDQAAQAAAgCsAEBwSEwABAAAIDACEQAAIIKAAAAMIAQAAAAAIRGAAAgNABGCAEEQSAADAAQCwISBAUBAoQQMQARACADAIQIEEAAYAAAAAA=="
)


def subset_indices() -> np.ndarray:
    packed = np.frombuffer(base64.b64decode(S_BITSET_B64), dtype=np.uint8)
    membership = np.unpackbits(packed, bitorder="little")[:N10]
    answer = np.flatnonzero(membership).astype(np.int32)
    if len(answer) != 1439:
        raise AssertionError(len(answer))
    digest = hashlib.sha256(answer.astype("<i4", copy=False).tobytes()).hexdigest()
    if digest != "b95a542c016ccfa9ded23ae4728e061dbcac9b9cda91a6dd35fbc7f039b3e04d":
        raise AssertionError(digest)
    return answer


def check(d11_cache: Path, horn_dual: Path) -> dict[str, object]:
    subset = subset_indices()
    data = np.load(d11_cache)
    if (int(data["n10"]), int(data["n11"])) != (N10, N11):
        raise AssertionError("wrong D11 shape")
    count = np.rint(11 * data["val"]).astype(np.int8)
    if not np.array_equal(count.astype(float) / 11, data["val"]):
        raise AssertionError("non-integral deletion-marginal entry")
    indicator = np.zeros(N10, dtype=np.int8)
    indicator[subset] = 1
    integer_matrix = csr_matrix(
        (count, (data["row"], data["col"])), shape=(N10, N11)
    )
    selected_deletions = np.asarray(integer_matrix.T @ indicator).ravel().astype(int)
    column_totals = np.asarray(integer_matrix.sum(axis=0)).ravel().astype(int)
    if not np.all(column_totals == 11):
        raise AssertionError((column_totals.min(), column_totals.max()))
    maximum = int(selected_deletions.max())
    if maximum > 6:
        raise AssertionError(maximum)

    with horn_dual.open("rb") as handle:
        payload = pickle.load(handle)
    raw_q = payload["x"][:N10]
    exact_q = [Fraction.from_float(max(0.0, float(value))) for value in raw_q]
    total = sum(exact_q, Fraction())
    selected = sum((exact_q[int(i)] for i in subset), Fraction())
    # Normalize only conceptually: selected/total > 6/11.
    gap_numerator = 11 * selected - 6 * total
    if gap_numerator <= 0:
        raise AssertionError("frozen optimizer does not violate the separator")

    histogram = np.bincount(selected_deletions, minlength=12)
    return {
        "verdict": "PASS",
        "subset_size": int(len(subset)),
        "subset_index_sha256": hashlib.sha256(
            subset.astype("<i4", copy=False).tobytes()
        ).hexdigest(),
        "max_selected_deletions_per_T11_type": maximum,
        "selected_deletion_histogram": histogram.tolist(),
        "universal_upper_bound": "6/11",
        "frozen_q_selected_mass_float": float(selected / total),
        "frozen_q_gap_over_6_11_float": float(selected / total - Fraction(6, 11)),
        "exact_positive_gap_numerator": gap_numerator.numerator,
        "exact_positive_gap_denominator": gap_numerator.denominator,
    }


def write_manifest(path: Path) -> dict[str, object]:
    subset = subset_indices()
    lines = geng_lines(10)
    if len(lines) != N10:
        raise AssertionError(len(lines))
    canonical = canonicalize(lines)
    entries = [
        {
            "index": int(i),
            "geng_graph6": lines[int(i)],
            "canonical_graph6": canonical[int(i)],
        }
        for i in subset
    ]
    payload = {
        "enumeration": "/opt/homebrew/bin/geng -q -t 10",
        "canonicalizer": "/opt/homebrew/bin/labelg -q -g",
        "subset_index_sha256": "b95a542c016ccfa9ded23ae4728e061dbcac9b9cda91a6dd35fbc7f039b3e04d",
        "entries": entries,
    }
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    return {"path": str(path), "entries": len(entries)}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("d11_cache", type=Path)
    parser.add_argument(
        "--horn-dual",
        type=Path,
        default=Path("compute23/src/anc/horn_dual.pkl"),
    )
    parser.add_argument("--write-manifest", type=Path)
    args = parser.parse_args()
    result = check(args.d11_cache, args.horn_dual)
    if args.write_manifest is not None:
        result["manifest"] = write_manifest(args.write_manifest)
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
