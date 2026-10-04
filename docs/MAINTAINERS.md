# Collaboration launch checklist

Repository files provide the contribution process; the settings below must be
configured on GitHub by a repository administrator. This checklist does not
assert that those settings are already enabled.

1. Review and publish the collaboration changes. Confirm **Build BC4lean** and
   **Check blueprint** succeed on a PR before selecting required checks.
2. Protect `main` with a branch rule/ruleset requiring PRs and the **Build project**
   and **Build blueprint HTML** checks. Consider requiring one approving review
   once another active reviewer is available; do not create a review requirement
   that the current team cannot satisfy. Keep force pushes disabled.
3. Confirm **Publish blueprint** is the active publisher. The legacy
   **Build and Deploy Pages** workflow (`deploy-pages.yml`) deploys a different
   `website/` tree and has automatic triggers in its source. Keep it disabled in
   GitHub Actions until the publishers are intentionally consolidated, otherwise
   it can overwrite the project homepage. Its remote enabled/disabled state has
   not been checked as part of preparing these documents.
4. Set a genuine private reporting contact in `CODE_OF_CONDUCT.md`; the existing
   `[ADD CONTACT METHOD]` placeholder has not been replaced with an invented
   address. This remains a launch item until the maintainer supplies a contact.
5. Turn agreed roadmap entries into issues, one bounded result per issue. Use
   difficulty labels only after reviewing prerequisites; constructing a universal
   proper space is not a beginner task. A project board is optional.
6. Credit merged contributions and invite regular reviewers to help maintain
   specific areas. Adding collaborators, changing access, transferring the repo,
   or creating an organization are separate owner decisions. Public fork/PR
   contributions do not require such a transfer.

Use `pull_request` workflows with read-only permissions for contribution checks.
Do not run untrusted PR code in a privileged `pull_request_target` workflow.
A first-time contributor's run may require maintainer approval under the
repository's Actions settings.

References:

- [GitHub: required status checks and skipped workflows](https://docs.github.com/en/pull-requests/how-tos/merge-and-close-pull-requests/troubleshooting-required-status-checks)
- [GitHub: protected branches](https://docs.github.com/en/repositories/configuring-branches-and-merges-in-your-repository/managing-protected-branches/about-protected-branches)
- [GitHub: Actions settings](https://docs.github.com/en/repositories/managing-your-repositorys-settings-and-features/enabling-features-for-your-repository/managing-github-actions-settings-for-a-repository)
