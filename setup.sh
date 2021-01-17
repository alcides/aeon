pip3 install yapf

if [[ "$OSTYPE" == "darwin"* ]]; then
    python3 -m pip install numpy==1.18.0 --user
fi
pip3 install -r requirements.pip



curl -o pre-commit.sh https://raw.githubusercontent.com/google/yapf/master/plugins/pre-commit.sh
chmod a+x pre-commit.sh
mv pre-commit.sh .git/hooks/pre-commit



