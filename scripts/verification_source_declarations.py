"""Small source scanner for theorem declarations audited by the Lean CI."""

from __future__ import annotations

import re
from collections.abc import Iterator


NAMESPACE_DECLARATION = re.compile(r"^namespace\s+([A-Za-z0-9_.]+)\s*$")
END_DECLARATION = re.compile(r"^end(?:\s+[A-Za-z0-9_]+)?\s*$")
THEOREM_DECLARATION = re.compile(
    r"^(?P<modifiers>(?:(?:private|protected|unsafe|noncomputable|partial|local)\s+)*)"
    r"theorem\s+(?P<name>[^\s:({]+)"
)


def _remove_attribute_prefix(text: str) -> tuple[str, bool]:
    """Remove complete leading `@[...]` attributes; report an open attribute."""
    remaining = text.lstrip()
    while remaining.startswith("@["):
        closing = remaining.find("]")
        if closing < 0:
            return "", True
        remaining = remaining[closing + 1 :].lstrip()
    return remaining, False


def theorem_declarations(lines: list[str]) -> Iterator[tuple[str, str, bool]]:
    """Yield `(namespace, name, is_private)` for line-start theorem declarations.

    Leading attributes may share a line with a declaration or span several lines.
    Common Lean declaration modifiers are accepted before `theorem`.
    """
    namespace_stack: list[str] = []
    pending_attribute = False
    for line in lines:
        stripped = line.strip()
        namespace = NAMESPACE_DECLARATION.match(stripped)
        if namespace:
            namespace_stack.append(namespace.group(1))
            pending_attribute = False
            continue
        if END_DECLARATION.match(stripped):
            if namespace_stack:
                namespace_stack.pop()
            pending_attribute = False
            continue

        if pending_attribute:
            closing = stripped.find("]")
            if closing < 0:
                continue
            stripped = stripped[closing + 1 :].lstrip()
            pending_attribute = False

        stripped, has_open_attribute = _remove_attribute_prefix(stripped)
        if has_open_attribute:
            pending_attribute = True
            continue
        match = THEOREM_DECLARATION.match(stripped)
        if match and namespace_stack:
            yield (
                ".".join(namespace_stack),
                match.group("name"),
                "private" in match.group("modifiers").split(),
            )
