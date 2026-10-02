#!/usr/bin/env python3
"""Check every generated page of site/ for broken links, broken HTML and textual glitches.

Prints one line per kind of problem with a count and examples, and exits with
status 1 when anything is found. Run it after build.py.
"""
import collections
import html.parser
import os
import re
import sys

SITE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "site")
BLOCK = {"p", "div", "li", "dt", "dd", "h1", "h2", "h3", "td", "th", "tr", "br", "ul", "ol", "table", "section",
         "header", "footer", "nav", "pre", "summary", "details", "main", "form", "label", "option", "select", "button",
         "svg", "title", "figure", "figcaption"}
VOID = {"area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta", "source", "track", "wbr"}
GLITCHES = [
    ("singular with plural noun", re.compile(r"(?<![\d,.])\b1 (semigroups|identities|varieties|entries|files|lines|"
                                             r"others|generators|classes|idempotents)\b")),
    ("leaked placeholder", re.compile(r"\b(undefined|NaN|nan)\b|\{[a-z_]+\}|\bNone\b(?! of)|(?<!a )\bnull\b(?! semigroup)")),
    ("space before punctuation", re.compile(r" [,.;:)](?!\d)")),
    ("double space", re.compile(r"\S  +\S")),
    ("repeated word", re.compile(r"\b(a|an|the|of|in|is|and|to)\s+\1\b", re.I)),
    ("double full stop", re.compile(r"(?<!\.)\.\.(?!\.)")),
]


class Checker(html.parser.HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.stack, self.errors, self.text, self.links, self.ids = [], [], [], [], []
        self.h1 = 0
        self.title = ""
        self.skip = 0
        self.in_title = False

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if tag in BLOCK:
            self.text.append(" ")
        if tag not in VOID:
            self.stack.append(tag)
        if tag in ("script", "style", "pre"):          # code is not prose
            self.skip += 1
        if tag == "h1":
            self.h1 += 1
        if tag == "title":
            self.in_title = True
        for key in ("href", "src", "data-src"):
            if attrs.get(key):
                self.links.append(attrs[key])
        if attrs.get("id"):
            self.ids.append(attrs["id"])

    def handle_endtag(self, tag):
        if tag in BLOCK:
            self.text.append(" ")
        if tag in VOID:
            return
        if tag in ("script", "style", "pre"):
            self.skip -= 1
        if tag == "title":
            self.in_title = False
        if not self.stack or self.stack[-1] != tag:
            self.errors.append(f"</{tag}> closes <{self.stack[-1] if self.stack else 'nothing'}>")
            if tag in self.stack:
                while self.stack and self.stack.pop() != tag:
                    pass
            return
        self.stack.pop()

    def handle_data(self, data):
        if self.in_title:
            self.title += data
        if not self.skip:
            self.text.append(data)


def main():
    problems = collections.defaultdict(list)
    files = set()
    for directory, _, names in os.walk(SITE):
        for name in names:
            files.add(os.path.relpath(os.path.join(directory, name), SITE))
    pages = sorted(f for f in files if f.endswith(".html"))
    for page in pages:
        with open(os.path.join(SITE, page), encoding="utf-8") as handle:
            source = handle.read()
        checker = Checker()
        checker.feed(source)
        checker.close()
        for error in checker.errors[:3]:
            problems["html nesting"].append(f"{page}: {error}")
        if checker.stack:
            problems["unclosed tags"].append(f"{page}: {checker.stack[-3:]}")
        if checker.h1 != 1:
            problems["not exactly one h1"].append(page)
        if not checker.title.strip():
            problems["no title"].append(page)
        for ident, count in collections.Counter(checker.ids).items():
            if count > 1:
                problems["duplicate id"].append(f"{page}: {ident}")
        for link in checker.links:
            if re.match(r"^(https?:|mailto:|data:|#)", link):
                continue
            target = os.path.normpath(os.path.join(os.path.dirname(page), link.split("#")[0].split("?")[0]))
            if target not in files:
                problems["broken link"].append(f"{page}: {link}")
        for tag, attrs in re.findall(r"<(ul|ol|dd|li|p|h2|h3|td)((?: [^>]*)?)>\s*</\1>", source):
            if "id=" not in attrs:                      # elements with an id are filled by a script
                problems[f"empty <{tag}>"].append(page)
        text = re.sub(r"\s+", " ", "".join(checker.text))
        for label, pattern in GLITCHES:
            for match in pattern.finditer(text):
                start = max(0, match.start() - 40)
                problems[label].append(f"{page}: …{text[start:match.end() + 30]}…")
    print(f"{len(pages)} pages checked")
    for label, items in sorted(problems.items()):
        print(f"{label}: {len(items)}")
        for item in items[:6]:
            print("   ", item)
    sys.exit(1 if problems else 0)


if __name__ == "__main__":
    main()
