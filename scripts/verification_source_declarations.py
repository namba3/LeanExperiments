"""Fail-closed lexical discovery for named Lean theorem declarations.

This is deliberately not a Lean parser. It recognizes declaration headers and
scope commands after removing Lean comments and strings. Unsupported or
unbalanced scope/attribute syntax raises ``ValueError`` so CI cannot silently
skip a file whose declarations it failed to understand.
"""

from __future__ import annotations

import re
from collections.abc import Iterator


NAMESPACE_DECLARATION = re.compile(
    r"^namespace\s+([A-Za-z0-9_'.]+(?:\.[A-Za-z0-9_']+)*)\s*$"
)
SECTION_DECLARATION = re.compile(r"^section(?:\s+([A-Za-z0-9_']+))?\s*$")
END_DECLARATION = re.compile(r"^end(?:\s+([A-Za-z0-9_'.]+))?\s*$")
DECLARATION = re.compile(
    r"^(?P<modifiers>(?:(?:private|protected|unsafe|noncomputable|partial|local|public)\s+)*)"
    r"(?P<kind>theorem|lemma)\s+(?P<name>[^\s:({]+)"
)
AD_HOC_AXIOM_DECLARATION = re.compile(
    r"^(?P<modifiers>(?:(?:private|protected|unsafe|noncomputable|partial|local|public)\s+)*)"
    r"(?P<kind>axiom|constant)\b"
)
MODIFIER_ONLY = re.compile(
    r"^(?:(?:private|protected|unsafe|noncomputable|partial|local|public)\s+)*"
    r"(?:private|protected|unsafe|noncomputable|partial|local|public)\s*$"
)


def strip_comments_and_strings(text: str) -> str:
    """Replace comments and string contents with spaces, preserving newlines."""
    output = list(text)
    index = 0
    block_depth = 0
    in_string = False
    escaped = False
    line_comment = False

    while index < len(text):
        current = text[index]
        following = text[index + 1] if index + 1 < len(text) else ""

        if line_comment:
            if current == "\n":
                line_comment = False
            else:
                output[index] = " "
            index += 1
            continue

        if block_depth:
            if current == "/" and following == "-":
                output[index] = output[index + 1] = " "
                block_depth += 1
                index += 2
            elif current == "-" and following == "/":
                output[index] = output[index + 1] = " "
                block_depth -= 1
                index += 2
            else:
                if current != "\n":
                    output[index] = " "
                index += 1
            continue

        if in_string:
            if current != "\n":
                output[index] = " "
            if escaped:
                escaped = False
            elif current == "\\":
                escaped = True
            elif current == '"':
                in_string = False
            index += 1
            continue

        if current == "-" and following == "-":
            output[index] = output[index + 1] = " "
            line_comment = True
            index += 2
        elif current == "/" and following == "-":
            output[index] = output[index + 1] = " "
            block_depth = 1
            index += 2
        elif current == '"':
            output[index] = " "
            in_string = True
            index += 1
        else:
            index += 1

    if block_depth:
        raise ValueError("unterminated Lean block comment")
    if in_string:
        raise ValueError("unterminated Lean string literal")
    return "".join(output)


def _remove_attribute_prefix(text: str) -> tuple[str, int]:
    """Remove balanced leading attributes; report an attribute spanning lines."""
    remaining = text.lstrip()
    while remaining.startswith("@["):
        depth = 1
        closing = None
        for index, character in enumerate(remaining[2:], start=2):
            if character == "[":
                depth += 1
            elif character == "]":
                depth -= 1
                if depth == 0:
                    closing = index
                    break
        if closing is None:
            return "", depth
        remaining = remaining[closing + 1 :].lstrip()
    return remaining, 0


def _continue_attribute(text: str, depth: int) -> tuple[str, int]:
    for index, character in enumerate(text):
        if character == "[":
            depth += 1
        elif character == "]":
            depth -= 1
            if depth == 0:
                return text[index + 1 :], 0
    return "", depth


def _current_namespace(scopes: list[tuple[str, str]]) -> str:
    return ".".join(name for kind, name in scopes if kind == "namespace")


def declared_namespaces(lines: list[str]) -> set[str]:
    """Return namespace commands outside comments and string literals."""
    source = strip_comments_and_strings("\n".join(lines))
    return {
        match.group(1)
        for line in source.splitlines()
        if (match := NAMESPACE_DECLARATION.match(line.strip()))
    }


def theorem_declarations(lines: list[str]) -> Iterator[tuple[str, str, bool]]:
    """Yield ``(namespace, name, is_private)`` for named theorem/lemma headers.

    Comments and strings cannot create phantom declarations. Namespace and
    section scopes are tracked independently, including qualified ``end``
    labels. Attributes and declaration modifiers may continue on later lines.
    """
    source = strip_comments_and_strings("\n".join(lines))
    scopes: list[tuple[str, str]] = []
    pending_attribute_depth = 0
    pending_modifiers: list[str] = []

    for line_number, line in enumerate(source.splitlines(), start=1):
        stripped = line.strip()
        if not stripped:
            continue

        namespace = NAMESPACE_DECLARATION.match(stripped)
        if namespace:
            scopes.append(("namespace", namespace.group(1)))
            pending_attribute_depth = 0
            pending_modifiers.clear()
            continue

        section = SECTION_DECLARATION.match(stripped)
        if section:
            scopes.append(("section", section.group(1) or ""))
            pending_attribute_depth = 0
            pending_modifiers.clear()
            continue

        end = END_DECLARATION.match(stripped)
        if end:
            if not scopes:
                raise ValueError(f"line {line_number}: `end` has no open namespace or section")
            label = end.group(1)
            if label is None:
                scopes.pop()
            else:
                matching = next(
                    (
                        index
                        for index in range(len(scopes) - 1, -1, -1)
                        if scopes[index][1] == label
                    ),
                    None,
                )
                if matching is None:
                    raise ValueError(
                        f"line {line_number}: `end {label}` does not match an open scope"
                    )
                del scopes[matching:]
            pending_attribute_depth = 0
            pending_modifiers.clear()
            continue

        if pending_attribute_depth:
            remainder, pending_attribute_depth = _continue_attribute(
                stripped, pending_attribute_depth
            )
            if pending_attribute_depth:
                continue
            stripped = remainder.lstrip()

        stripped, pending_attribute_depth = _remove_attribute_prefix(stripped)
        if pending_attribute_depth:
            continue
        if not stripped:
            continue

        if MODIFIER_ONLY.fullmatch(stripped):
            pending_modifiers.extend(stripped.split())
            continue

        header = " ".join([*pending_modifiers, stripped])
        match = DECLARATION.match(header)
        pending_modifiers.clear()
        if match:
            # A valid header may contain only one theorem command on its
            # physical line. Do not silently classify the first declaration
            # while overlooking a second command after a separator.
            if re.search(r"\b(?:theorem|lemma)\b", header[match.end() :]):
                raise ValueError(
                    f"line {line_number}: multiple theorem/lemma commands on one line"
                )
            namespace_name = _current_namespace(scopes)
            yield (
                namespace_name,
                match.group("name"),
                "private" in match.group("modifiers").split(),
            )
        elif re.search(r"\b(?:theorem|lemma)\b", stripped):
            raise ValueError(
                f"line {line_number}: theorem/lemma keyword is not at a recognized declaration header"
            )

    if pending_attribute_depth:
        raise ValueError("unterminated Lean attribute")
    if pending_modifiers:
        raise ValueError("declaration modifiers are not followed by a theorem or lemma")
    if scopes:
        kind, name = scopes[-1]
        label = f" {name}" if name else ""
        raise ValueError(f"unclosed Lean {kind}{label}")


def ad_hoc_axiom_declarations(lines: list[str]) -> Iterator[tuple[int, str]]:
    """Yield source lines declaring `axiom` or `constant`, including attributes."""
    source = strip_comments_and_strings("\n".join(lines))
    pending_attribute_depth = 0
    pending_modifiers: list[str] = []
    for line_number, line in enumerate(source.splitlines(), start=1):
        stripped = line.strip()
        if not stripped:
            continue
        if pending_attribute_depth:
            remainder, pending_attribute_depth = _continue_attribute(
                stripped, pending_attribute_depth
            )
            if pending_attribute_depth:
                continue
            stripped = remainder.lstrip()
        stripped, pending_attribute_depth = _remove_attribute_prefix(stripped)
        if pending_attribute_depth:
            continue
        if not stripped:
            continue
        if MODIFIER_ONLY.fullmatch(stripped):
            pending_modifiers.extend(stripped.split())
            continue
        header = " ".join([*pending_modifiers, stripped])
        match = AD_HOC_AXIOM_DECLARATION.match(header)
        pending_modifiers.clear()
        if match:
            if re.search(r"\b(?:axiom|constant)\b", header[match.end() :]):
                raise ValueError(
                    f"line {line_number}: multiple axiom/constant commands on one line"
                )
            yield line_number, match.group("kind")
        elif re.search(r"\b(?:axiom|constant)\b", stripped):
            raise ValueError(
                f"line {line_number}: axiom/constant keyword is not at a recognized declaration header"
            )

    if pending_attribute_depth:
        raise ValueError("unterminated Lean attribute")
    if pending_modifiers:
        raise ValueError("declaration modifiers are not followed by a declaration")
