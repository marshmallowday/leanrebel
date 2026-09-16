"""One-time M01-B assembly: store four already hash-reviewed Git blobs.

No branch, commit, PR, or upstream repository is mutated by this program.
The GitHub plugin attaches returned blob IDs to the reviewed final tree.
This temporary writer and its workflow are removed before main integration.
"""
import base64
import hashlib
import json
import os
from pathlib import Path
import urllib.request

REPO = 'marshmallowday/leanrebel'
if os.environ.get('GITHUB_REPOSITORY') != REPO or os.environ.get('GITHUB_REF') != 'refs/heads/rebel/m01-b':
    raise SystemExit('Only the authorized fork-local assembly branch is permitted')
expected = {
    'official-tree.txt': '20f86aaac33ff8eba5a6b5a3f3b4015011bffb80976cf0ce392f84966522853b',
    'official.json.gz': '802333959487fac1624c27d387d4a33cf778e15f739863591071f506ae7e7c2b',
    'reuse.json': '9f0b64815db8fedda0445c2fd66ad0cbb11d176e95d3c6aee878c07b9011459e',
    'sources.json': '33f5358406b87465d797885dd7832acf965c6e50dbfa4d3cac5026687eed8213',
}
files = {}
for name, sha in expected.items():
    raw = (Path('docs/rebel/inventory') / name).read_bytes()
    if hashlib.sha256(raw).hexdigest() != sha:
        raise SystemExit('Reproduction differs from reviewed bytes: ' + name)
    files[name] = raw
records = []
for name, raw in files.items():
    request = urllib.request.Request(
        'https://api.github.com/repos/' + REPO + '/git/blobs',
        data=json.dumps({'content': base64.b64encode(raw).decode(), 'encoding': 'base64'}).encode(),
        headers={'Authorization': 'Bearer ' + os.environ['GH_TOKEN'],
                 'Accept': 'application/vnd.github+json',
                 'X-GitHub-Api-Version': '2022-11-28', 'Content-Type': 'application/json'},
        method='POST')
    with urllib.request.urlopen(request, timeout=60) as response:
        result = json.load(response)
    local_sha = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
    if result['sha'] != local_sha:
        raise SystemExit('Git blob hash mismatch: ' + name)
    records.append({'path': 'docs/rebel/inventory/' + name, 'sha': local_sha,
                    'sha256': expected[name], 'bytes': len(raw)})
output = json.dumps({'source_commit': os.environ['GITHUB_SHA'], 'blobs': records}, indent=2)
Path(os.environ['RUNNER_TEMP'], 'm01-generated-blobs.json').write_text(output + '\n')
print(output)
print('M01_GENERATED_BLOBS_PASS; no branch or commit was changed')
