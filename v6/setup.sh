apt update
apt install software-properties-common
add-apt-repository ppa:sri-csl/formal-methods
curl -sL https://deb.nodesource.com/setup_10.x | sudo -E bash -
apt install gcc nano screen nodejs yices2 yices2-dev
wget https://dl.google.com/go/go1.10.3.linux-amd64.tar.gz
cd /opt
tar xvf ~/go1.10.3.linux-amd64.tar.gz
echo "
export GOROOT=/opt/go
export PATH=$GOROOT/bin:$PATH
" > ~/.bash_profile
source ~/.bash_profile
