# provenstream (the host package)

The Python package of [Provenstream](https://github.com/eloquentsh/provenstream): the generic host that runs
streams whose rules are proved in Lean 4, the pipeline that builds a proof revision into an engine, and the
`provenstream` command line (a client of a host, or the host in process on a local database).

Install it with `pip install ./host` from a checkout (`pip install './host[postgres,keyring,test]'` for the Postgres
store, the system keychain and the test dependencies), or run it uninstalled with `bin/provenstream`.

The repository's README explains what a stream is, what is proved and what is trusted; `docs/hosting.md` explains
running a host. This package is MIT licensed, as the repository is: its LICENSE file is a copy of the repository's.
