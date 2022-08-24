#!/bin/bash -i

## Fix issues with gitpod's stock .bashrc
cp /etc/skel/.bashrc $HOME

## Shorthands for git
git config --global alias.slog 'log --pretty=oneline --abbrev-commit'
git config --global alias.co checkout
git config --global alias.lco '!f() { git checkout ":/$1:" ; }; f'

## Waste less screen estate on the prompt.
echo 'export PS1="$ "' >> $HOME/.bashrc

## Make it easy to go back and forth in the (linear) git history.
echo 'function sn() { git log --reverse --pretty=%H main | grep -A 1 $(git rev-parse HEAD) | tail -n1 | xargs git show --color; }' >> $HOME/.bashrc
echo 'function n() { git log --reverse --pretty=%H main | grep -A 1 $(git rev-parse HEAD) | tail -n1 | xargs git checkout; }' >> $HOME/.bashrc
echo 'function p() { git checkout HEAD^; }' >> $HOME/.bashrc

## Place to install TLC, TLAPS, Apalache, ...
mkdir -p tools

## PATH below has two locations because of inconsistencies between Gitpod and Codespaces.
## Gitpod:     /workspace/...
## Codespaces: /workspaces/...

## Install TLA+ Tools (download from github instead of nightly.tlapl.us (inria) to only rely on github)
wget -qN https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar -P tools/
echo "alias tlcrepl='java -cp /workspace/Examples/tools/tla2tools.jar:/workspaces/Examples/tools/tla2tools.jar tlc2.REPL'" >> $HOME/.bashrc
echo "alias tlc='java -cp /workspace/Examples/tools/tla2tools.jar:/workspaces/Examples/tools/tla2tools.jar tlc2.TLC'" >> $HOME/.bashrc

## Install CommunityModules
wget -qN https://github.com/tlaplus/CommunityModules/releases/latest/download/CommunityModules-deps.jar -P tools/

## Install graphvix and latex deps
sudo apt-get install -y graphviz htop
sudo apt-get install -y --no-install-recommends texlive-latex-recommended
