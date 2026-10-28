#!/bin/sh
# Copy the build that GitHub Pages serves to the faculty server, so that both copies of the site are the same files,
# then compare build.json of both live copies. Run it after pushing to main, once the Pages workflow has succeeded.
set -eu
cd "$(dirname "$0")"
head=$(git rev-parse HEAD)
run=$(gh run list --workflow pages.yml --commit "$head" --status success --json databaseId --jq '.[0].databaseId')
if [ -z "$run" ]; then
  echo "no successful Pages run for $head yet" >&2
  exit 1
fi
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
gh run download "$run" --name github-pages --dir "$tmp"
mkdir "$tmp/site"
tar -xf "$tmp/artifact.tar" -C "$tmp/site"
built=$(python3 -c 'import json, sys; r = json.load(open(sys.argv[1])); assert r["site_commit"] == sys.argv[2], r; print(r["content_sha256"])' "$tmp/site/build.json" "$head")
rsync -rlz --delete --chmod=Du=rwx,Dgo=rx,Fu=rw,Fgo=r "$tmp/site/" bnaskrecki@lts-faculty.wmi.amu.edu.pl:public_html/semigroups6/
status=0
for url in https://nasqret.github.io/semibase-site https://bnaskrecki.faculty.wmi.amu.edu.pl/semigroups6; do
  live=$(curl -fsS "$url/build.json?t=$(date +%s)" | python3 -c 'import json, sys; print(json.load(sys.stdin)["content_sha256"])' || echo none)
  if [ "$live" = "$built" ]; then echo "in sync: $url"; else echo "DIFFERENT: $url serves $live, the build is $built"; status=1; fi
done
exit $status
