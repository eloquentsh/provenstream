# Engine mutants of the solo change control layer

Written by `tests/mutants.py` (2026-11-04). 17 rule mutants and 50 order mutants of `Layer.lean`, each built as an engine and run against the state machine of `test_sequences.py` with the real model as oracle.
67 mutants: 62 killed, 5 survived (5 predicted equivalent), 0 did not build; as predicted


## rule-only_opener_can_create

only_opener_can_create never refuses. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '1a568d4e-1340-5ea7-b3d5-5c53367f8651', 'command': {'command': 'change.create', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'from_revision_url': 'https://example.org/repo/commit/r0'}, 'fresh': []}, {'stream_id'`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.branch stream_id=7A7D2A53-0C3B-5458-8FA4-B90AB455DE86 change_id=0b70800b developer_id=77aab131 branch_revision_url= meta=a	b -> malformed
1a568d4e change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted   <-- the model wanted only_opener_can_create
```

## rule-change_id_must_be_new

change_id_must_be_new never refuses. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.create', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'from_revision_url': 'https://example.org/repo/commit/r1'}, 'fresh': []}, {'stream_id'`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.open proof_revision_url=https://example.org/provenstream/commit/0123456789abcdef -> revision_url_must_name_a_commit
77aab131 stream.close stream_id=35a91c91 -> stream_must_exist
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b developer_id=77aab131 branch_revision_url= meta=a	b -> malformed
77aab131 change.branch stream_id=7A7D2A53-0C3B-5458-8FA4-B90AB455DE86 change_id=0b70800b developer_id=77aab131 branch_revision_url= meta=a	b -> malformed
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.review stream_id=35a91c91 change_id=0b70800b reviewed_revision_url=r0 screen_url=https://example.org/screens/s0 -> stream_must_exist
77aab131 change.abandon stream_id=7A7D2A53-0C3B-5458-8FA4-B90AB455DE86 change_id=0b70800b meta=a	b -> malformed
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r1 -> accepted   <-- the model wanted change_id_must_be_new
```

## rule-change_must_exist

change_must_exist never refuses. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'branch_revision_url': 'https://example.org/repo/commit/r0', 'developer_id': '1a568d4e`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=1a568d4e -> accepted   <-- the model wanted change_must_exist
```

## rule-revisions_must_be_unique

revisions_must_be_unique never refuses. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'branch_revision_url': 'https://example.org/repo/commit/r0', 'developer_id': '1a568d4e`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=1a568d4e -> accepted   <-- the model wanted revisions_must_be_unique
```

## rule-only_opener_can_branch

only_opener_can_branch never refuses. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '1a568d4e-1340-5ea7-b3d5-5c53367f8651', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'branch_revision_url': 'https://example.org/repo/commit/r1', 'developer_id': '77aab131`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol meta=a	b extra=1 -> malformed
77aab131 stream.close stream_id=35a91c91 -> stream_must_exist
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.merge stream_id=7a7d2a53 change_id=0b70800b merged_revision_url=r0 -> revisions_must_be_unique
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r1 developer_id=77aab131 -> developer_must_not_be_the_opener   <-- the model wanted only_opener_can_branch
```

## rule-developer_must_not_be_the_opener

developer_must_not_be_the_opener never refuses. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'branch_revision_url': 'https://example.org/repo/commit/r1', 'developer_id': '77aab131`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
1a568d4e stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
1a568d4e stream.close stream_id=35a91c91 -> accepted
77aab131 stream.close stream_id=35a91c91 -> stream_must_be_open
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r1 developer_id=77aab131 -> accepted   <-- the model wanted developer_must_not_be_the_opener
```

## rule-developer_is_branched_once

developer_is_branched_once never refuses. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'branch_revision_url': 'https://example.org/repo/commit/b1', 'developer_id': '1a568d4e`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol meta=a	b -> malformed
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.push stream_id=35a91c91 change_id=0b70800b pushed_revision_url=r0 -> stream_must_exist
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=r1 screen_url=https://example.org/screens/s0 meta=a	b -> malformed
77aab131 change.pull stream_id=7a7d2a53 change_id=0b70800b meta=a	b -> malformed
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=r1 screen_url=https://example.org/screens/s0 meta=a	b -> malformed
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=1a568d4e -> revisions_must_be_unique
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r1 -> change_id_must_be_new
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=77aab131 -> revisions_must_be_unique
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r1 developer_id=77aab131 -> only_opener_can_branch
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r1 developer_id=77aab131 -> only_opener_can_branch
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=1a568d4e -> revisions_must_be_unique
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r1 developer_id=77aab131 -> only_opener_can_branch
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r1 developer_id=77aab131 -> only_opener_can_branch
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b developer_id=1a568d4e branch_revision_url=r1 -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=b1 developer_id=1a568d4e -> accepted   <-- the model wanted developer_is_branched_once
```

## rule-developer_must_not_be_a_reviewer

developer_must_not_be_a_reviewer never refuses. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'branch_revision_url': 'https://example.org/repo/commit/b2', 'developer_id': '7d8726d7`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.open proof_revision_url=https://example.org/provenstream/commit/0123456789abcdef -> revision_url_must_name_a_commit
77aab131 stream.close stream_id=35a91c91 -> stream_must_exist
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 harness_revision_url=null -> accepted
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=r1 screen_url=https://example.org/screens/s0 -> accepted
7d8726d7 change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=b1 screen_url=https://example.org/screens/s0 -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=b2 developer_id=7d8726d7 -> accepted   <-- the model wanted developer_must_not_be_a_reviewer
```

## rule-change_must_not_be_pulled

change_must_not_be_pulled never refuses. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'branch_revision_url': 'https://example.org/repo/commit/b3', 'developer_id': 'be284532`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.open proof_revision_url=https://example.org/provenstream/commit/0123456789abcdef -> revision_url_must_name_a_commit
77aab131 stream.close stream_id=35a91c91 -> stream_must_exist
1a568d4e stream.close stream_id=7a7d2a53 -> only_opener_can_close
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 harness_revision_url=null -> accepted
77aab131 change.push stream_id=7A7D2A53-0C3B-5458-8FA4-B90AB455DE86 change_id=0b70800b pushed_revision_url= meta=a	b -> malformed
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b developer_id=1a568d4e branch_revision_url=r1 -> accepted
1a568d4e change.push stream_id=7a7d2a53 change_id=0b70800b pushed_revision_url=b1 meta=a	b -> malformed
7d8726d7 change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url= screen_url=https://example.org/screens/s0 meta=a	b -> malformed
7d8726d7 change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=b1 screen_url=https://example.org/screens/s0 -> accepted
3078b569 change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=b2 screen_url=https://example.org/screens/s0 -> accepted
7d8726d7 change.review stream_id=7A7D2A53-0C3B-5458-8FA4-B90AB455DE86 change_id=0b70800b reviewed_revision_url= screen_url=https://example.org/screens/s0 meta=a	b -> malformed
77aab131 change.pull stream_id=7a7d2a53 change_id=0b70800b -> accepted
7d8726d7 change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=b3 screen_url=https://example.org/screens/s0 meta=a	b -> malformed
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=b3 developer_id=be284532 -> accepted   <-- the model wanted change_must_not_be_pulled
```

## rule-only_branched_developers_can_push

only_branched_developers_can_push never refuses. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.push', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'pushed_revision_url': 'https://example.org/repo/commit/r1'}, 'fresh': []}, {'stream_id'`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.close stream_id=35a91c91 -> stream_must_exist
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=1a568d4e -> revisions_must_be_unique
1a568d4e stream.close stream_id=7a7d2a53 -> only_opener_can_close
77aab131 change.create stream_id=35a91c91 change_id=0b70800b from_revision_url=r0 -> stream_must_exist
77aab131 change.push stream_id=7a7d2a53 change_id=0b70800b pushed_revision_url=r1 -> accepted   <-- the model wanted only_branched_developers_can_push
```

## rule-only_opener_can_pull

only_opener_can_pull never refuses. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '1a568d4e-1340-5ea7-b3d5-5c53367f8651', 'command': {'command': 'change.pull', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446'}, 'fresh': []}, {'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'event': {'stream_i`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
1a568d4e change.pull stream_id=7a7d2a53 change_id=0b70800b -> accepted   <-- the model wanted only_opener_can_pull
```

## rule-change_is_pulled_once

change_is_pulled_once never refuses. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.pull', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446'}, 'fresh': []}, {'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'event': {'stream_i`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=1a568d4e -> revisions_must_be_unique
77aab131 change.branch stream_id=7a7d2a53 change_id=5249aeca branch_revision_url=r0 developer_id=77aab131 -> change_must_exist
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=r1 screen_url=https://example.org/screens/s0 -> accepted
77aab131 change.pull stream_id=7a7d2a53 change_id=0b70800b -> accepted
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=b1 screen_url=https://example.org/screens/s0 meta=a	b -> malformed
77aab131 change.pull stream_id=7a7d2a53 change_id=0b70800b -> accepted   <-- the model wanted change_is_pulled_once
```

## rule-reviewer_must_not_be_a_developer

reviewer_must_not_be_a_developer never refuses. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '1a568d4e-1340-5ea7-b3d5-5c53367f8651', 'command': {'command': 'change.review', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'reviewed_revision_url': 'https://example.org/repo/commit/b2', 'screen_url': 'https://`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.open proof_revision_url=https://example.org/provenstream/commit/0123456789abcdef -> revision_url_must_name_a_commit
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.push stream_id=35a91c91 change_id=0b70800b pushed_revision_url=r0 -> stream_must_exist
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b developer_id=1a568d4e branch_revision_url=r1 -> accepted
1a568d4e change.push stream_id=7a7d2a53 change_id=0b70800b pushed_revision_url=b1 -> accepted
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=b2 screen_url=https://example.org/screens/s0 -> accepted   <-- the model wanted reviewer_must_not_be_a_developer
```

## rule-reviewer_must_not_be_the_opener

reviewer_must_not_be_the_opener never refuses. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.review', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'reviewed_revision_url': 'https://example.org/repo/commit/r1', 'screen_url': 'https://`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=r1 screen_url=https://example.org/screens/s0 -> accepted   <-- the model wanted reviewer_must_not_be_the_opener
```

## rule-only_opener_can_decide

only_opener_can_decide never refuses. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '1a568d4e-1340-5ea7-b3d5-5c53367f8651', 'command': {'command': 'change.merge', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'merged_revision_url': 'https://example.org/repo/commit/r1'}, 'fresh': []}, {'stream_id`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.open proof_revision_url=https://example.org/provenstream/commit/0123456789abcdef -> revision_url_must_name_a_commit
77aab131 stream.close stream_id=35a91c91 -> stream_must_exist
1a568d4e stream.close stream_id=7a7d2a53 -> only_opener_can_close
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
1a568d4e change.merge stream_id=7a7d2a53 change_id=0b70800b merged_revision_url=r1 -> accepted   <-- the model wanted only_opener_can_decide
```

## rule-change_is_decided_once

change_is_decided_once never refuses. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.merge', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'merged_revision_url': 'https://example.org/repo/commit/b3'}, 'fresh': []}, {'stream_id`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.open proof_revision_url=https://example.org/provenstream/commit/0123456789abcdef -> revision_url_must_name_a_commit
77aab131 stream.close stream_id=35a91c91 -> stream_must_exist
1a568d4e stream.close stream_id=7a7d2a53 -> only_opener_can_close
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.push stream_id=7a7d2a53 change_id=0b70800b pushed_revision_url=r1 -> only_branched_developers_can_push
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=r1 screen_url=https://example.org/screens/s0 -> accepted
77aab131 change.pull stream_id=7a7d2a53 change_id=0b70800b -> accepted
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=b1 screen_url=https://example.org/screens/s0 -> accepted
77aab131 change.branch stream_id=35a91c91 change_id=0b70800b branch_revision_url=r0 developer_id=77aab131 -> stream_must_exist
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=1a568d4e -> revisions_must_be_unique
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> stream_id_must_be_new
77aab131 change.merge stream_id=7a7d2a53 change_id=0b70800b merged_revision_url=b2 -> accepted
77aab131 change.create stream_id=7a7d2a53 change_id=5249aeca from_revision_url=b2 meta=a	b -> malformed
77aab131 change.create stream_id=7a7d2a53 change_id=5249aeca from_revision_url=r0 -> accepted
77aab131 change.merge stream_id=7a7d2a53 change_id=0b70800b merged_revision_url=b3 -> accepted   <-- the model wanted change_is_decided_once
```

## rule-change_must_be_undecided

change_must_be_undecided never refuses. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'branch_revision_url': 'https://example.org/repo/commit/b2', 'developer_id': '7d8726d7`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.open proof_revision_url=https://example.org/provenstream/commit/0123456789abcdef -> revision_url_must_name_a_commit
77aab131 stream.close stream_id=35a91c91 -> stream_must_exist
1a568d4e stream.close stream_id=7a7d2a53 -> only_opener_can_close
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.push stream_id=7a7d2a53 change_id=0b70800b pushed_revision_url=r1 -> only_branched_developers_can_push
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=r1 screen_url=https://example.org/screens/s0 meta=a	b -> malformed
77aab131 change.pull stream_id=7a7d2a53 change_id=0b70800b meta=a	b -> malformed
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=r1 screen_url=https://example.org/screens/s0 -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=b1 developer_id=1a568d4e -> developer_must_not_be_a_reviewer
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=1a568d4e -> revisions_must_be_unique
77aab131 change.merge stream_id=7a7d2a53 change_id=0b70800b merged_revision_url=b1 -> accepted
77aab131 change.create stream_id=7a7d2a53 change_id=5249aeca from_revision_url=b1 meta=a	b -> malformed
77aab131 change.create stream_id=7a7d2a53 change_id=5249aeca from_revision_url=r0 -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=b2 developer_id=7d8726d7 -> accepted   <-- the model wanted change_must_be_undecided
```

## swap-only_opener_can_create-change_id_must_be_new

only_opener_can_create and change_id_must_be_new swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '1a568d4e-1340-5ea7-b3d5-5c53367f8651', 'command': {'command': 'change.create', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'from_revision_url': 'https://example.org/repo/commit/r0', 'harness_revision_url': Non`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 harness_revision_url=null -> accepted
1a568d4e change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 harness_revision_url=null -> change_id_must_be_new   <-- the model wanted only_opener_can_create
```

## swap-change_must_exist-revisions_must_be_unique

change_must_exist and revisions_must_be_unique swapped. **survived, as predicted: equivalent**.

- change_must_exist / revisions_must_be_unique: a note on a change exists only once the change is created (every_event_names_a_created_change), so revisions_must_be_unique cannot fail where change_must_exist fails

## swap-change_must_exist-only_opener_can_branch

change_must_exist and only_opener_can_branch swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '1a568d4e-1340-5ea7-b3d5-5c53367f8651', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'developer_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'branch_revision_url': 'https:`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b developer_id=77aab131 branch_revision_url=r0 -> only_opener_can_branch   <-- the model wanted change_must_exist
```

## swap-change_must_exist-developer_must_not_be_the_opener

change_must_exist and developer_must_not_be_the_opener swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '5249aeca-f459-5285-95a4-49f1e2e666a4', 'branch_revision_url': 'https://example.org/repo/commit/r0', 'developer_id': '77aab131`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.branch stream_id=7A7D2A53-0C3B-5458-8FA4-B90AB455DE86 change_id=0b70800b developer_id=77aab131 branch_revision_url= meta=a	b -> malformed
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 harness_revision_url=null -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=5249aeca branch_revision_url=r0 developer_id=77aab131 -> developer_must_not_be_the_opener   <-- the model wanted change_must_exist
```

## swap-change_must_exist-developer_is_branched_once

change_must_exist and developer_is_branched_once swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'developer_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'branch_revision_url': 'https:`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b developer_id=77aab131 branch_revision_url=r0 -> developer_must_not_be_the_opener   <-- the model wanted change_must_exist
```

## swap-change_must_exist-developer_must_not_be_a_reviewer

change_must_exist and developer_must_not_be_a_reviewer swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'developer_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'branch_revision_url': 'https:`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b developer_id=77aab131 branch_revision_url=r0 -> developer_must_not_be_the_opener   <-- the model wanted change_must_exist
```

## swap-change_must_exist-change_must_not_be_pulled

change_must_exist and change_must_not_be_pulled swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'developer_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'branch_revision_url': 'https:`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b developer_id=77aab131 branch_revision_url=r0 -> developer_must_not_be_the_opener   <-- the model wanted change_must_exist
```

## swap-change_must_exist-only_branched_developers_can_push

change_must_exist and only_branched_developers_can_push swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.push', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '5249aeca-f459-5285-95a4-49f1e2e666a4', 'pushed_revision_url': 'https://example.org/repo/commit/r0'}, 'fresh': []}, {'stream_id'`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
1a568d4e stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.merge stream_id=7a7d2a53 change_id=0b70800b merged_revision_url=r0 -> revisions_must_be_unique
77aab131 change.push stream_id=7a7d2a53 change_id=5249aeca pushed_revision_url=r0 -> only_branched_developers_can_push   <-- the model wanted change_must_exist
```

## swap-change_must_exist-only_opener_can_pull

change_must_exist and only_opener_can_pull swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.push', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '5249aeca-f459-5285-95a4-49f1e2e666a4', 'pushed_revision_url': 'https://example.org/repo/commit/r0'}, 'fresh': []}, {'stream_id'`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
1a568d4e stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.merge stream_id=7a7d2a53 change_id=0b70800b merged_revision_url=r0 -> revisions_must_be_unique
77aab131 change.push stream_id=7a7d2a53 change_id=5249aeca pushed_revision_url=r0 -> only_branched_developers_can_push   <-- the model wanted change_must_exist
```

## swap-change_must_exist-change_is_pulled_once

change_must_exist and change_is_pulled_once swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.push', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '5249aeca-f459-5285-95a4-49f1e2e666a4', 'pushed_revision_url': 'https://example.org/repo/commit/r0'}, 'fresh': []}, {'stream_id'`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
1a568d4e stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.merge stream_id=7a7d2a53 change_id=0b70800b merged_revision_url=r0 -> revisions_must_be_unique
77aab131 change.push stream_id=7a7d2a53 change_id=5249aeca pushed_revision_url=r0 -> only_branched_developers_can_push   <-- the model wanted change_must_exist
```

## swap-change_must_exist-reviewer_must_not_be_a_developer

change_must_exist and reviewer_must_not_be_a_developer swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.push', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '5249aeca-f459-5285-95a4-49f1e2e666a4', 'pushed_revision_url': 'https://example.org/repo/commit/r0'}, 'fresh': []}, {'stream_id'`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
1a568d4e stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.merge stream_id=7a7d2a53 change_id=0b70800b merged_revision_url=r0 -> revisions_must_be_unique
77aab131 change.push stream_id=7a7d2a53 change_id=5249aeca pushed_revision_url=r0 -> only_branched_developers_can_push   <-- the model wanted change_must_exist
```

## swap-change_must_exist-reviewer_must_not_be_the_opener

change_must_exist and reviewer_must_not_be_the_opener swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '1a568d4e-1340-5ea7-b3d5-5c53367f8651', 'command': {'command': 'change.push', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'pushed_revision_url': 'https://example.org/repo/commit/r0'}, 'fresh': []}, {'stream_id'`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.open proof_revision_url=https://example.org/provenstream/commit/0123456789abcdef -> revision_url_must_name_a_commit
1a568d4e change.push stream_id=7a7d2a53 change_id=0b70800b pushed_revision_url=r0 -> only_branched_developers_can_push   <-- the model wanted change_must_exist
```

## swap-change_must_exist-only_opener_can_decide

change_must_exist and only_opener_can_decide swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '1a568d4e-1340-5ea7-b3d5-5c53367f8651', 'command': {'command': 'change.push', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'pushed_revision_url': 'https://example.org/repo/commit/r0'}, 'fresh': []}, {'stream_id'`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.open proof_revision_url=https://example.org/provenstream/commit/0123456789abcdef -> revision_url_must_name_a_commit
1a568d4e change.push stream_id=7a7d2a53 change_id=0b70800b pushed_revision_url=r0 -> only_branched_developers_can_push   <-- the model wanted change_must_exist
```

## swap-change_must_exist-change_is_decided_once

change_must_exist and change_is_decided_once swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '1a568d4e-1340-5ea7-b3d5-5c53367f8651', 'command': {'command': 'change.push', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'pushed_revision_url': 'https://example.org/repo/commit/r0'}, 'fresh': []}, {'stream_id'`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.open proof_revision_url=https://example.org/provenstream/commit/0123456789abcdef -> revision_url_must_name_a_commit
1a568d4e change.push stream_id=7a7d2a53 change_id=0b70800b pushed_revision_url=r0 -> only_branched_developers_can_push   <-- the model wanted change_must_exist
```

## swap-change_must_exist-change_must_be_undecided

change_must_exist and change_must_be_undecided swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '1a568d4e-1340-5ea7-b3d5-5c53367f8651', 'command': {'command': 'change.abandon', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '5249aeca-f459-5285-95a4-49f1e2e666a4'}, 'fresh': []}, {'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'reason': 'only_`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.open proof_revision_url=https://example.org/provenstream/commit/0123456789abcdef -> revision_url_must_name_a_commit
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.pull stream_id=35a91c91 change_id=0b70800b -> stream_must_exist
1a568d4e change.abandon stream_id=7a7d2a53 change_id=5249aeca -> only_opener_can_decide   <-- the model wanted change_must_exist
```

## swap-revisions_must_be_unique-only_opener_can_branch

revisions_must_be_unique and only_opener_can_branch swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '1a568d4e-1340-5ea7-b3d5-5c53367f8651', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'branch_revision_url': 'https://example.org/repo/commit/r0', 'developer_id': '1a568d4e`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
1a568d4e stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r1 developer_id=77aab131 -> developer_must_not_be_the_opener
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=1a568d4e -> only_opener_can_branch   <-- the model wanted revisions_must_be_unique
```

## swap-revisions_must_be_unique-developer_must_not_be_the_opener

revisions_must_be_unique and developer_must_not_be_the_opener swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '1a568d4e-1340-5ea7-b3d5-5c53367f8651', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'branch_revision_url': 'https://example.org/repo/commit/r0', 'developer_id': '1a568d4e`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.merge stream_id=7a7d2a53 change_id=0b70800b merged_revision_url=r0 -> revisions_must_be_unique
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=1a568d4e -> only_opener_can_branch   <-- the model wanted revisions_must_be_unique
```

## swap-revisions_must_be_unique-developer_is_branched_once

revisions_must_be_unique and developer_is_branched_once swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'branch_revision_url': 'https://example.org/repo/commit/r0', 'developer_id': '77aab131`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
1a568d4e stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
1a568d4e stream.close stream_id=35a91c91 -> accepted
77aab131 stream.close stream_id=35a91c91 -> stream_must_be_open
1a568d4e stream.close stream_id=7a7d2a53 -> only_opener_can_close
77aab131 change.create stream_id=35a91c91 change_id=0b70800b from_revision_url=r0 -> stream_must_be_open
77aab131 change.create stream_id=35a91c91 change_id=0b70800b from_revision_url=r0 -> stream_must_be_open
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
1a568d4e change.abandon stream_id=7a7d2a53 change_id=0b70800b -> only_opener_can_decide
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=77aab131 -> developer_must_not_be_the_opener   <-- the model wanted revisions_must_be_unique
```

## swap-revisions_must_be_unique-developer_must_not_be_a_reviewer

revisions_must_be_unique and developer_must_not_be_a_reviewer swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '1a568d4e-1340-5ea7-b3d5-5c53367f8651', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'branch_revision_url': 'https://example.org/repo/commit/r0', 'developer_id': '1a568d4e`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b developer_id=77aab131 branch_revision_url= meta=a	b -> malformed
77aab131 change.branch stream_id=7A7D2A53-0C3B-5458-8FA4-B90AB455DE86 change_id=0b70800b developer_id=77aab131 branch_revision_url= meta=a	b -> malformed
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r1 developer_id=77aab131 -> developer_must_not_be_the_opener
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=1a568d4e -> only_opener_can_branch   <-- the model wanted revisions_must_be_unique
```

## swap-revisions_must_be_unique-change_must_not_be_pulled

revisions_must_be_unique and change_must_not_be_pulled swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'branch_revision_url': 'https://example.org/repo/commit/r0', 'developer_id': '77aab131`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.open proof_revision_url=https://example.org/provenstream/commit/0123456789abcdef -> revision_url_must_name_a_commit
77aab131 stream.close stream_id=35a91c91 -> stream_must_exist
1a568d4e stream.close stream_id=7a7d2a53 -> only_opener_can_close
1a568d4e stream.close stream_id=7a7d2a53 -> only_opener_can_close
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.push stream_id=35a91c91 change_id=0b70800b pushed_revision_url=r0 -> stream_must_exist
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=77aab131 -> developer_must_not_be_the_opener   <-- the model wanted revisions_must_be_unique
```

## swap-revisions_must_be_unique-only_branched_developers_can_push

revisions_must_be_unique and only_branched_developers_can_push swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '1a568d4e-1340-5ea7-b3d5-5c53367f8651', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'branch_revision_url': 'https://example.org/repo/commit/r0', 'developer_id': '1a568d4e`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b developer_id=77aab131 branch_revision_url= meta=a	b -> malformed
77aab131 change.branch stream_id=7A7D2A53-0C3B-5458-8FA4-B90AB455DE86 change_id=0b70800b developer_id=77aab131 branch_revision_url= meta=a	b -> malformed
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r1 developer_id=77aab131 -> developer_must_not_be_the_opener
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=1a568d4e -> only_opener_can_branch   <-- the model wanted revisions_must_be_unique
```

## swap-revisions_must_be_unique-reviewer_must_not_be_a_developer

revisions_must_be_unique and reviewer_must_not_be_a_developer swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.push', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'pushed_revision_url': 'https://example.org/repo/commit/r0'}, 'fresh': []}, {'stream_id'`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b developer_id=77aab131 branch_revision_url= meta=a	b -> malformed
77aab131 change.branch stream_id=7A7D2A53-0C3B-5458-8FA4-B90AB455DE86 change_id=0b70800b developer_id=77aab131 branch_revision_url= meta=a	b -> malformed
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> stream_id_must_be_new
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r1 developer_id=1a568d4e -> only_opener_can_branch
77aab131 change.push stream_id=7a7d2a53 change_id=0b70800b pushed_revision_url=r0 -> only_branched_developers_can_push   <-- the model wanted revisions_must_be_unique
```

## swap-revisions_must_be_unique-reviewer_must_not_be_the_opener

revisions_must_be_unique and reviewer_must_not_be_the_opener swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.push', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'pushed_revision_url': 'https://example.org/repo/commit/r0'}, 'fresh': []}, {'stream_id'`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b developer_id=77aab131 branch_revision_url= meta=a	b -> malformed
77aab131 change.branch stream_id=7A7D2A53-0C3B-5458-8FA4-B90AB455DE86 change_id=0b70800b developer_id=77aab131 branch_revision_url= meta=a	b -> malformed
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> stream_id_must_be_new
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r1 developer_id=1a568d4e -> only_opener_can_branch
77aab131 change.push stream_id=7a7d2a53 change_id=0b70800b pushed_revision_url=r0 -> only_branched_developers_can_push   <-- the model wanted revisions_must_be_unique
```

## swap-revisions_must_be_unique-only_opener_can_decide

revisions_must_be_unique and only_opener_can_decide swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.push', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'pushed_revision_url': 'https://example.org/repo/commit/r0'}, 'fresh': []}, {'stream_id'`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b developer_id=77aab131 branch_revision_url= meta=a	b -> malformed
77aab131 change.branch stream_id=7A7D2A53-0C3B-5458-8FA4-B90AB455DE86 change_id=0b70800b developer_id=77aab131 branch_revision_url= meta=a	b -> malformed
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> stream_id_must_be_new
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r1 developer_id=1a568d4e -> only_opener_can_branch
77aab131 change.push stream_id=7a7d2a53 change_id=0b70800b pushed_revision_url=r0 -> only_branched_developers_can_push   <-- the model wanted revisions_must_be_unique
```

## swap-revisions_must_be_unique-change_is_decided_once

revisions_must_be_unique and change_is_decided_once swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.push', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'pushed_revision_url': 'https://example.org/repo/commit/r0'}, 'fresh': []}, {'stream_id'`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b developer_id=77aab131 branch_revision_url= meta=a	b -> malformed
77aab131 change.branch stream_id=7A7D2A53-0C3B-5458-8FA4-B90AB455DE86 change_id=0b70800b developer_id=77aab131 branch_revision_url= meta=a	b -> malformed
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> stream_id_must_be_new
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r1 developer_id=1a568d4e -> only_opener_can_branch
77aab131 change.push stream_id=7a7d2a53 change_id=0b70800b pushed_revision_url=r0 -> only_branched_developers_can_push   <-- the model wanted revisions_must_be_unique
```

## swap-revisions_must_be_unique-change_must_be_undecided

revisions_must_be_unique and change_must_be_undecided swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '1a568d4e-1340-5ea7-b3d5-5c53367f8651', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'branch_revision_url': 'https://example.org/repo/commit/r0', 'developer_id': '1a568d4e`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
1a568d4e change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> only_opener_can_create
77aab131 stream.close stream_id=35a91c91 -> stream_must_exist
1a568d4e stream.close stream_id=7a7d2a53 -> only_opener_can_close
1a568d4e stream.close stream_id=7a7d2a53 -> only_opener_can_close
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r1 developer_id=1a568d4e -> only_opener_can_branch
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=1a568d4e -> only_opener_can_branch   <-- the model wanted revisions_must_be_unique
```

## swap-only_opener_can_branch-developer_must_not_be_the_opener

only_opener_can_branch and developer_must_not_be_the_opener swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '1a568d4e-1340-5ea7-b3d5-5c53367f8651', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'developer_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'branch_revision_url': 'https:`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.open proof_revision_url=https://example.org/provenstream/commit/0123456789abcdef -> revision_url_must_name_a_commit
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=1a568d4e -> revisions_must_be_unique
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b developer_id=77aab131 branch_revision_url=r1 -> developer_must_not_be_the_opener   <-- the model wanted only_opener_can_branch
```

## swap-only_opener_can_branch-developer_is_branched_once

only_opener_can_branch and developer_is_branched_once swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '1a568d4e-1340-5ea7-b3d5-5c53367f8651', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'developer_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'branch_revision_url': 'https:`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.open proof_revision_url=https://example.org/provenstream/commit/0123456789abcdef -> revision_url_must_name_a_commit
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=1a568d4e -> revisions_must_be_unique
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b developer_id=77aab131 branch_revision_url=r1 -> developer_must_not_be_the_opener   <-- the model wanted only_opener_can_branch
```

## swap-only_opener_can_branch-developer_must_not_be_a_reviewer

only_opener_can_branch and developer_must_not_be_a_reviewer swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '1a568d4e-1340-5ea7-b3d5-5c53367f8651', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'branch_revision_url': 'https://example.org/repo/commit/r1', 'developer_id': '77aab131`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.open proof_revision_url=https://example.org/provenstream/commit/0123456789abcdef -> revision_url_must_name_a_commit
77aab131 stream.close stream_id=35a91c91 -> stream_must_exist
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 harness_revision_url=null -> accepted
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r1 developer_id=77aab131 -> developer_must_not_be_the_opener   <-- the model wanted only_opener_can_branch
```

## swap-only_opener_can_branch-change_must_not_be_pulled

only_opener_can_branch and change_must_not_be_pulled swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '1a568d4e-1340-5ea7-b3d5-5c53367f8651', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'branch_revision_url': 'https://example.org/repo/commit/r1', 'developer_id': '77aab131`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol meta=a	b extra=1 -> malformed
77aab131 stream.close stream_id=35a91c91 -> stream_must_exist
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.merge stream_id=7a7d2a53 change_id=0b70800b merged_revision_url=r0 -> revisions_must_be_unique
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r1 developer_id=77aab131 -> developer_must_not_be_the_opener   <-- the model wanted only_opener_can_branch
```

## swap-only_opener_can_branch-change_must_be_undecided

only_opener_can_branch and change_must_be_undecided swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '1a568d4e-1340-5ea7-b3d5-5c53367f8651', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'branch_revision_url': 'https://example.org/repo/commit/r1', 'developer_id': '77aab131`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol meta=a	b extra=1 -> malformed
77aab131 stream.close stream_id=35a91c91 -> stream_must_exist
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.merge stream_id=7a7d2a53 change_id=0b70800b merged_revision_url=r0 -> revisions_must_be_unique
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r1 developer_id=77aab131 -> developer_must_not_be_the_opener   <-- the model wanted only_opener_can_branch
```

## swap-developer_must_not_be_the_opener-developer_is_branched_once

developer_must_not_be_the_opener and developer_is_branched_once swapped. **survived, as predicted: equivalent**.

- developer_must_not_be_the_opener / developer_is_branched_once: the opener is never a developer (no_developer_is_the_opener)

## swap-developer_must_not_be_the_opener-developer_must_not_be_a_reviewer

developer_must_not_be_the_opener and developer_must_not_be_a_reviewer swapped. **survived, as predicted: equivalent**.

- developer_must_not_be_the_opener / developer_must_not_be_a_reviewer: the opener is never a reviewer (no_reviewer_is_the_opener)
- developer_must_not_be_the_opener / developer_is_branched_once: the opener is never a developer (no_developer_is_the_opener)
- developer_is_branched_once / developer_must_not_be_a_reviewer: nobody is both a developer and a reviewer of a change (roles_are_disjoint)

## swap-developer_must_not_be_the_opener-change_must_not_be_pulled

developer_must_not_be_the_opener and change_must_not_be_pulled swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'branch_revision_url': 'https://example.org/repo/commit/b2', 'developer_id': '1a568d4e`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
1a568d4e stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.branch stream_id=7A7D2A53-0C3B-5458-8FA4-B90AB455DE86 change_id=0b70800b developer_id=77aab131 branch_revision_url= meta=a	b -> malformed
1a568d4e stream.close stream_id=35a91c91 -> accepted
77aab131 stream.close stream_id=35a91c91 -> stream_must_be_open
77aab131 change.create stream_id=35a91c91 change_id=0b70800b from_revision_url=r0 -> stream_must_be_open
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=1a568d4e -> revisions_must_be_unique
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r1 -> change_id_must_be_new
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=77aab131 -> revisions_must_be_unique
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r1 developer_id=77aab131 -> only_opener_can_branch
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r1 developer_id=77aab131 -> only_opener_can_branch
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=1a568d4e -> revisions_must_be_unique
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r1 developer_id=77aab131 -> only_opener_can_branch
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r1 developer_id=77aab131 -> developer_must_not_be_the_opener
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=r1 screen_url=https://example.org/screens/s0 -> accepted
77aab131 change.pull stream_id=7a7d2a53 change_id=0b70800b -> accepted
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=b1 screen_url=https://example.org/screens/s0 -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=b2 developer_id=1a568d4e -> change_must_not_be_pulled   <-- the model wanted developer_must_not_be_a_reviewer
```

## swap-developer_must_not_be_the_opener-change_must_be_undecided

developer_must_not_be_the_opener and change_must_be_undecided swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'branch_revision_url': 'https://example.org/repo/commit/b1', 'developer_id': '77aab131`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.open proof_revision_url=https://example.org/provenstream/commit/0123456789abcdef -> revision_url_must_name_a_commit
77aab131 stream.close stream_id=35a91c91 -> stream_must_exist
1a568d4e stream.close stream_id=7a7d2a53 -> only_opener_can_close
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
1a568d4e change.pull stream_id=7a7d2a53 change_id=0b70800b -> only_opener_can_pull
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=1a568d4e -> revisions_must_be_unique
77aab131 change.push stream_id=7a7d2a53 change_id=0b70800b pushed_revision_url=r0 -> revisions_must_be_unique
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=r1 screen_url=https://example.org/screens/s0 meta=a	b -> malformed
77aab131 change.pull stream_id=7a7d2a53 change_id=0b70800b meta=a	b -> malformed
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=r1 screen_url=https://example.org/screens/s0 meta=a	b -> malformed
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=r1 screen_url=https://example.org/screens/s0 -> accepted
77aab131 change.pull stream_id=7a7d2a53 change_id=0b70800b -> accepted
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=b1 screen_url=https://example.org/screens/s0 meta=a	b -> malformed
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=b1 developer_id=77aab131 -> change_must_not_be_pulled   <-- the model wanted developer_must_not_be_the_opener
```

## swap-developer_is_branched_once-developer_must_not_be_a_reviewer

developer_is_branched_once and developer_must_not_be_a_reviewer swapped. **survived, as predicted: equivalent**.

- developer_is_branched_once / developer_must_not_be_a_reviewer: nobody is both a developer and a reviewer of a change (roles_are_disjoint)

## swap-developer_is_branched_once-change_must_not_be_pulled

developer_is_branched_once and change_must_not_be_pulled swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'branch_revision_url': 'https://example.org/repo/commit/b2', 'developer_id': '1a568d4e`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.pull stream_id=35a91c91 change_id=0b70800b -> stream_must_exist
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=r1 screen_url=https://example.org/screens/s0 -> accepted
77aab131 change.pull stream_id=7a7d2a53 change_id=0b70800b meta=a	b -> malformed
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=b1 screen_url=https://example.org/screens/s0 -> accepted
77aab131 change.pull stream_id=7a7d2a53 change_id=0b70800b -> accepted
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=b2 screen_url=https://example.org/screens/s0 meta=a	b -> malformed
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=b2 developer_id=1a568d4e -> change_must_not_be_pulled   <-- the model wanted developer_must_not_be_a_reviewer
```

## swap-developer_is_branched_once-change_must_be_undecided

developer_is_branched_once and change_must_be_undecided swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.pull', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446'}, 'fresh': []}, {'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'reason': 'change_m`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=1a568d4e -> revisions_must_be_unique
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=r1 screen_url=https://example.org/screens/s0 -> accepted
77aab131 change.pull stream_id=7a7d2a53 change_id=0b70800b -> accepted
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=b1 screen_url=https://example.org/screens/s0 meta=a	b -> malformed
77aab131 change.merge stream_id=7a7d2a53 change_id=0b70800b merged_revision_url=b1 -> accepted
77aab131 change.create stream_id=7a7d2a53 change_id=5249aeca from_revision_url=b1 meta=a	b -> malformed
77aab131 change.pull stream_id=7a7d2a53 change_id=0b70800b -> change_must_be_undecided   <-- the model wanted change_is_pulled_once
```

## swap-developer_must_not_be_a_reviewer-change_must_not_be_pulled

developer_must_not_be_a_reviewer and change_must_not_be_pulled swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.branch', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'branch_revision_url': 'https://example.org/repo/commit/b1', 'developer_id': '1a568d4e`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.merge stream_id=7a7d2a53 change_id=0b70800b merged_revision_url=r0 -> revisions_must_be_unique
1a568d4e stream.close stream_id=7a7d2a53 -> only_opener_can_close
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=r1 screen_url=https://example.org/screens/s0 -> accepted
77aab131 change.pull stream_id=7a7d2a53 change_id=0b70800b -> accepted
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=b1 screen_url=https://example.org/screens/s0 meta=a	b -> malformed
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=b1 developer_id=1a568d4e -> change_must_not_be_pulled   <-- the model wanted developer_must_not_be_a_reviewer
```

## swap-developer_must_not_be_a_reviewer-change_must_be_undecided

developer_must_not_be_a_reviewer and change_must_be_undecided swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.pull', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446'}, 'fresh': []}, {'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'reason': 'change_m`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=1a568d4e -> revisions_must_be_unique
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=r1 screen_url=https://example.org/screens/s0 -> accepted
77aab131 change.pull stream_id=7a7d2a53 change_id=0b70800b -> accepted
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=b1 screen_url=https://example.org/screens/s0 meta=a	b -> malformed
77aab131 change.merge stream_id=7a7d2a53 change_id=0b70800b merged_revision_url=b1 -> accepted
77aab131 change.create stream_id=7a7d2a53 change_id=5249aeca from_revision_url=b1 meta=a	b -> malformed
77aab131 change.pull stream_id=7a7d2a53 change_id=0b70800b -> change_must_be_undecided   <-- the model wanted change_is_pulled_once
```

## swap-change_must_not_be_pulled-only_branched_developers_can_push

change_must_not_be_pulled and only_branched_developers_can_push swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.push', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'pushed_revision_url': 'https://example.org/repo/commit/b2'}, 'fresh': []}, {'stream_id'`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol meta=a	b -> malformed
77aab131 change.branch stream_id=7A7D2A53-0C3B-5458-8FA4-B90AB455DE86 change_id=0b70800b developer_id=77aab131 branch_revision_url= meta=a	b -> malformed
1a568d4e stream.close stream_id=7a7d2a53 -> only_opener_can_close
1a568d4e stream.close stream_id=7a7d2a53 -> only_opener_can_close
77aab131 change.create stream_id=35a91c91 change_id=0b70800b from_revision_url=r0 -> stream_must_exist
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b developer_id=77aab131 branch_revision_url= -> malformed
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol extra=1 -> malformed
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.push stream_id=35a91c91 change_id=0b70800b pushed_revision_url=r0 -> stream_must_exist
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r1 developer_id=77aab131 -> only_opener_can_branch
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=1a568d4e -> revisions_must_be_unique
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=r1 screen_url=https://example.org/screens/s0 -> accepted
77aab131 change.pull stream_id=7a7d2a53 change_id=0b70800b -> accepted
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=b1 screen_url=https://example.org/screens/s0 -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=b2 developer_id=7d8726d7 -> change_must_not_be_pulled
77aab131 change.abandon stream_id=7a7d2a53 change_id=0b70800b meta=a	b -> malformed
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol meta=a	b extra=1 -> malformed
77aab131 change.push stream_id=35a91c91 change_id=0b70800b pushed_revision_url=r0 -> stream_must_exist
77aab131 change.push stream_id=7a7d2a53 change_id=0b70800b pushed_revision_url=b2 -> only_branched_developers_can_push   <-- the model wanted change_must_not_be_pulled
```

## swap-change_must_not_be_pulled-change_must_be_undecided

change_must_not_be_pulled and change_must_be_undecided swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.push', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'pushed_revision_url': 'https://example.org/repo/commit/b2'}, 'fresh': []}, {'stream_id'`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.open proof_revision_url=https://example.org/provenstream/commit/0123456789abcdef -> revision_url_must_name_a_commit
77aab131 stream.close stream_id=35a91c91 -> stream_must_exist
1a568d4e stream.close stream_id=7a7d2a53 -> only_opener_can_close
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=1a568d4e -> revisions_must_be_unique
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=r1 screen_url=https://example.org/screens/s0 -> accepted
77aab131 change.pull stream_id=7a7d2a53 change_id=0b70800b -> accepted
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=b1 screen_url=https://example.org/screens/s0 -> accepted
77aab131 change.push stream_id=7a7d2a53 change_id=0b70800b pushed_revision_url=b2 -> only_branched_developers_can_push   <-- the model wanted change_must_not_be_pulled
```

## swap-only_branched_developers_can_push-change_must_be_undecided

only_branched_developers_can_push and change_must_be_undecided swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.push', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'pushed_revision_url': 'https://example.org/repo/commit/b3'}, 'fresh': []}, {'stream_id'`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.open proof_revision_url=https://example.org/provenstream/commit/0123456789abcdef -> revision_url_must_name_a_commit
77aab131 change.create stream_id=7A7D2A53-0C3B-5458-8FA4-B90AB455DE86 change_id=0b70800b from_revision_url= harness_revision_url=null meta=a	b -> malformed
1a568d4e stream.close stream_id=7a7d2a53 -> only_opener_can_close
1a568d4e stream.close stream_id=7a7d2a53 -> only_opener_can_close
77aab131 change.branch stream_id=7A7D2A53-0C3B-5458-8FA4-B90AB455DE86 change_id=0b70800b developer_id=77aab131 branch_revision_url= meta=a	b -> malformed
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=r0 screen_url=https://example.org/screens/s0 -> revisions_must_be_unique
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r1 -> change_id_must_be_new
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=r1 screen_url=https://example.org/screens/s0 -> accepted
7d8726d7 change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=b1 screen_url=https://example.org/screens/s0 -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=7d8726d7 -> revisions_must_be_unique
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=b2 developer_id=77aab131 -> only_opener_can_branch
77aab131 change.merge stream_id=7a7d2a53 change_id=0b70800b merged_revision_url=b2 -> accepted
77aab131 change.push stream_id=7a7d2a53 change_id=0b70800b pushed_revision_url=b3 -> change_must_be_undecided   <-- the model wanted only_branched_developers_can_push
```

## swap-only_opener_can_pull-change_is_pulled_once

only_opener_can_pull and change_is_pulled_once swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '1a568d4e-1340-5ea7-b3d5-5c53367f8651', 'command': {'command': 'change.pull', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446'}, 'fresh': []}, {'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'reason': 'change_i`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r1 developer_id=77aab131 -> developer_must_not_be_the_opener
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=r1 screen_url=https://example.org/screens/s0 -> accepted
77aab131 change.pull stream_id=7a7d2a53 change_id=0b70800b -> accepted
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=b1 screen_url=https://example.org/screens/s0 -> accepted
1a568d4e change.pull stream_id=7a7d2a53 change_id=0b70800b -> change_is_pulled_once   <-- the model wanted only_opener_can_pull
```

## swap-only_opener_can_pull-change_must_be_undecided

only_opener_can_pull and change_must_be_undecided swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '1a568d4e-1340-5ea7-b3d5-5c53367f8651', 'command': {'command': 'change.pull', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446'}, 'fresh': []}, {'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'reason': 'change_i`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.open proof_revision_url=https://example.org/provenstream/commit/0123456789abcdef -> revision_url_must_name_a_commit
77aab131 stream.close stream_id=35a91c91 -> stream_must_exist
1a568d4e stream.close stream_id=7a7d2a53 -> only_opener_can_close
1a568d4e stream.close stream_id=7a7d2a53 -> only_opener_can_close
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=1a568d4e -> revisions_must_be_unique
77aab131 change.abandon stream_id=7a7d2a53 change_id=0b70800b meta=a	b -> malformed
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=r1 screen_url=https://example.org/screens/s0 meta=a	b -> malformed
77aab131 change.pull stream_id=7a7d2a53 change_id=0b70800b -> accepted
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=r1 screen_url=https://example.org/screens/s0 -> accepted
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=b1 developer_id=7d8726d7 -> change_must_not_be_pulled
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol meta=a	b -> malformed
1a568d4e change.pull stream_id=7a7d2a53 change_id=0b70800b -> change_is_pulled_once   <-- the model wanted only_opener_can_pull
```

## swap-change_is_pulled_once-change_must_be_undecided

change_is_pulled_once and change_must_be_undecided swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.pull', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446'}, 'fresh': []}, {'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'reason': 'change_m`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
1a568d4e change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> only_opener_can_create
77aab131 stream.close stream_id=35a91c91 -> stream_must_exist
1a568d4e stream.close stream_id=7a7d2a53 -> only_opener_can_close
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.push stream_id=7a7d2a53 change_id=0b70800b pushed_revision_url=r1 -> only_branched_developers_can_push
1a568d4e change.create stream_id=7a7d2a53 change_id=5249aeca from_revision_url=r0 -> only_opener_can_create
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=1a568d4e -> revisions_must_be_unique
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=r1 screen_url=https://example.org/screens/s0 -> accepted
77aab131 change.pull stream_id=7a7d2a53 change_id=0b70800b -> accepted
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=b1 screen_url=https://example.org/screens/s0 meta=a	b -> malformed
77aab131 change.merge stream_id=7a7d2a53 change_id=0b70800b merged_revision_url=b1 -> accepted
77aab131 change.create stream_id=7a7d2a53 change_id=5249aeca from_revision_url=b1 meta=a	b -> malformed
77aab131 change.review stream_id=7A7D2A53-0C3B-5458-8FA4-B90AB455DE86 change_id=0b70800b reviewed_revision_url=b2 screen_url=https://example.org/screens/s0 -> malformed
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> stream_id_must_be_new
77aab131 change.create stream_id=7a7d2a53 change_id=5249aeca from_revision_url=r0 -> accepted
77aab131 change.push stream_id=35a91c91 change_id=0b70800b pushed_revision_url=r0 -> stream_must_exist
77aab131 change.push stream_id=35a91c91 change_id=0b70800b pushed_revision_url=r0 -> stream_must_exist
77aab131 change.pull stream_id=7a7d2a53 change_id=0b70800b -> change_must_be_undecided   <-- the model wanted change_is_pulled_once
```

## swap-reviewer_must_not_be_a_developer-reviewer_must_not_be_the_opener

reviewer_must_not_be_a_developer and reviewer_must_not_be_the_opener swapped. **survived, as predicted: equivalent**.

- reviewer_must_not_be_a_developer / reviewer_must_not_be_the_opener: the opener is never a developer (no_developer_is_the_opener)

## swap-reviewer_must_not_be_a_developer-change_must_be_undecided

reviewer_must_not_be_a_developer and change_must_be_undecided swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.review', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'reviewed_revision_url': 'https://example.org/repo/commit/b2', 'screen_url': 'https://`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol meta=a	b extra=1 -> malformed
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.push stream_id=35a91c91 change_id=0b70800b pushed_revision_url=r0 -> stream_must_exist
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=1a568d4e -> revisions_must_be_unique
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol meta=a	b extra=1 -> malformed
1a568d4e change.create stream_id=7a7d2a53 change_id=5249aeca from_revision_url=r0 -> only_opener_can_create
77aab131 change.push stream_id=7a7d2a53 change_id=5249aeca pushed_revision_url=r0 -> change_must_exist
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r1 -> change_id_must_be_new
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=r1 screen_url=https://example.org/screens/s0 -> accepted
77aab131 change.pull stream_id=7a7d2a53 change_id=0b70800b meta=a	b -> malformed
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=b1 screen_url=https://example.org/screens/s0 meta=a	b -> malformed
77aab131 change.merge stream_id=7a7d2a53 change_id=0b70800b merged_revision_url=b1 -> accepted
77aab131 change.create stream_id=7a7d2a53 change_id=5249aeca from_revision_url=r0 -> accepted
1a568d4e change.branch stream_id=7a7d2a53 change_id=5249aeca branch_revision_url=r1 developer_id=1a568d4e -> only_opener_can_branch
77aab131 change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=b2 screen_url=https://example.org/screens/s0 -> change_must_be_undecided   <-- the model wanted reviewer_must_not_be_the_opener
```

## swap-reviewer_must_not_be_the_opener-change_must_be_undecided

reviewer_must_not_be_the_opener and change_must_be_undecided swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '77aab131-6d0b-5ae2-8461-e8a7f4d28084', 'command': {'command': 'change.review', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446', 'reviewed_revision_url': 'https://example.org/repo/commit/b2', 'screen_url': 'https://`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol meta=a	b extra=1 -> malformed
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
77aab131 change.push stream_id=35a91c91 change_id=0b70800b pushed_revision_url=r0 -> stream_must_exist
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r0 developer_id=1a568d4e -> revisions_must_be_unique
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol meta=a	b extra=1 -> malformed
1a568d4e change.create stream_id=7a7d2a53 change_id=5249aeca from_revision_url=r0 -> only_opener_can_create
77aab131 change.push stream_id=7a7d2a53 change_id=5249aeca pushed_revision_url=r0 -> change_must_exist
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r1 -> change_id_must_be_new
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=r1 screen_url=https://example.org/screens/s0 -> accepted
77aab131 change.pull stream_id=7a7d2a53 change_id=0b70800b meta=a	b -> malformed
1a568d4e change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=b1 screen_url=https://example.org/screens/s0 meta=a	b -> malformed
77aab131 change.merge stream_id=7a7d2a53 change_id=0b70800b merged_revision_url=b1 -> accepted
77aab131 change.create stream_id=7a7d2a53 change_id=5249aeca from_revision_url=r0 -> accepted
1a568d4e change.branch stream_id=7a7d2a53 change_id=5249aeca branch_revision_url=r1 developer_id=1a568d4e -> only_opener_can_branch
77aab131 change.review stream_id=7a7d2a53 change_id=0b70800b reviewed_revision_url=b2 screen_url=https://example.org/screens/s0 -> change_must_be_undecided   <-- the model wanted reviewer_must_not_be_the_opener
```

## swap-only_opener_can_decide-change_is_decided_once

only_opener_can_decide and change_is_decided_once swapped. **killed**.

Killed by (`AssertionError: ('the reason', {'actor_id': '1a568d4e-1340-5ea7-b3d5-5c53367f8651', 'command': {'command': 'change.abandon', 'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'change_id': '0b70800b-0b7d-5686-adc8-be6def4eb446'}, 'fresh': []}, {'stream_id': '7a7d2a53-0c3b-5458-8fa4-b90ab455de86', 'reason': 'chang`):

```
77aab131 stream.open proof_revision_url=https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol -> accepted
77aab131 stream.open proof_revision_url=https://example.org/provenstream/commit/0123456789abcdef -> revision_url_must_name_a_commit
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b developer_id=77aab131 branch_revision_url= meta=a	b -> malformed
77aab131 change.branch stream_id=7a7d2a53 change_id=0b70800b developer_id=77aab131 branch_revision_url= meta=a	b -> malformed
1a568d4e change.review stream_id=7A7D2A53-0C3B-5458-8FA4-B90AB455DE86 change_id=0b70800b reviewed_revision_url= screen_url=https://example.org/screens/s0 meta=a	b -> malformed
77aab131 change.create stream_id=7a7d2a53 change_id=0b70800b from_revision_url=r0 -> accepted
1a568d4e change.branch stream_id=7a7d2a53 change_id=0b70800b branch_revision_url=r1 developer_id=1a568d4e -> only_opener_can_branch
77aab131 change.merge stream_id=7a7d2a53 change_id=0b70800b merged_revision_url=r1 -> accepted
1a568d4e change.abandon stream_id=7a7d2a53 change_id=0b70800b -> change_is_decided_once   <-- the model wanted only_opener_can_decide
```
