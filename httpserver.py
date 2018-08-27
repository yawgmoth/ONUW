import BaseHTTPServer
import SocketServer
import threading
import time
import shutil
import os
import random
import hashlib
import sys
import traceback
import threading
import subprocess
from cgi import parse_header, parse_multipart
from urlparse import parse_qs

HOST_NAME = "127.0.0.1"
PORT_NUMBER = 31337

class Game:
    def __init__(self, fname):
        self.options = []
        self.output = []
        self.proc = subprocess.Popen(["rungameA.exe", fname], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, bufsize=1)
        self.thread = threading.Thread(target=self)
        self.thread.start()
        self.running = threading.Lock()
        self.actions = []
        self.has_options = threading.Semaphore(0)
        self.is_done = False
    def __call__(self):
        print("starting polling")
        lines = []
        cardmode = False
        resultmode = False
        l = ""
        while l.strip() != "Done.":
            l = self.proc.stdout.readline()
            print(l)
            items = l.split()
            if l.startswith("current phase:"):
                items = l.split(":")
                self.phase = items[1].strip().strip('"')
            elif l.startswith("Choose one of"):
                n = int(l.split()[3])                
                self.options = lines[-n:]
                self.output = lines[:-n]
                self.has_options.release()
                lines = []
            else:
                lines.append(l.strip())
            if len(items) > 1 and items[1] == "does:":                
                actor = items[0]
                action = " ".join(items[2:])
                self.actions.append((actor, action))

            time.sleep(0.01)
        self.output = lines
        self.has_options.release()
        self.is_done = True
    def get_options(self):
        self.has_options.acquire()
        result = self.options
        output = self.output
        actions = self.actions
        self.options = []
        self.output = []
        self.actions = []
        return (result,output,actions)
    def perform(self, i):
        print "perform", i
        self.proc.stdin.write("%d\n"%i)
        self.proc.stdin.flush()
    def finish(self):
        pass
    def done(self):
        return self.is_done
        
games = {}
gameslock = threading.Lock()

class MyHandler(BaseHTTPServer.BaseHTTPRequestHandler):
    def do_HEAD(s):
        s.send_response(200)
        s.send_header("Content-type", "text/html")
        s.end_headers()
    def do_GET(s):
        try:
            return s.perform_response()
        except Exception:
            print traceback.format_exc()
            
    def invalid(s, gid):
        if len(gid) != 16:
            return True
        for c in gid:
            if c not in "0123456789abcdef":
                return True
        if not os.path.exists("log/game%s.log"%gid):
            return True
        return False
    
    def perform_response(s):
        """Respond to a GET request."""
        global games
        
        game = None
        gid = None
        path = s.path
        if s.path.startswith("/gid"):
            gid = s.path[4:20]
            gameslock.acquire()
            print "got gid", gid, gid in games
            if gid in games:
                game = games[gid]
            gameslock.release()
            path = s.path[20:]
        elif s.path.startswith("/start/") or s.path == "/":
            game = Game(sys.argv[1])
            gid = s.getgid()
            gameslock.acquire()
            games[gid] = game
            gameslock.release()
        else:
            s.send_response(400)
            s.end_headers()
            return
        
        if s.path.startswith("/favicon"):
            s.send_response(200)
            s.end_headers()
            return
            
        if s.path.startswith("http://"): 
            s.send_response(400)
            s.end_headers()
            return
            
        if s.path.startswith("/robots.txt"):
            s.send_response(200)
            s.send_header("Content-type", "text/plain")
            s.end_headers()
            s.wfile.write("User-agent: *\n")
            s.wfile.write("Disallow: /\n")
            return
        
        if not game:
            s.send_response(400)
            s.end_headers()
            return
        
        s.send_response(200)
        s.send_header("Content-type", "text/html")
        s.end_headers()
        
        parts = path.strip("/").split("/")
        print parts
        if parts[0] == "do":
            index = int(parts[1])
            game.perform(index)
            
            
        s.wfile.write("<html><head><title>Ostari Web</title></head>\n")
        s.wfile.write('<body>\n')
        
        (options,output,actions) = game.get_options()
        s.wfile.write("<h2>Player actions</h2>\n")
        s.wfile.write("<table><tr><th>Actor</th><th>Action</th></tr>\n")
        for (actor,action) in actions:
            s.wfile.write("<tr><td>%s</td><td>%s</td></tr>\n"%(actor,action))
        s.wfile.write("</table>\n")
        if options:
            s.wfile.write("<h2>Choose an action</h2>\n")
            s.wfile.write("<ul>\n")
            for (i,opt) in enumerate(options):
                s.wfile.write('<li><a href="/gid%s/do/%d">%s</a></li>\n'%(gid,i,opt))
            s.wfile.write("</ul>\n")
        else:
            s.wfile.write("<h1>The End</h1>\n")
            s.wfile.write('<h2><a href="/start/">Restart</a></h2>\n')
        
        s.wfile.write('<p style="color: gray">\n')
        s.wfile.write("<h2>Output:</h2>\n")
        for out in output:
            s.wfile.write("%s<br/>\n"%out)
                   
        s.wfile.write("</p>\n")
       
        s.wfile.write("</body></html>\n")
        if game.done() and gid is not None and gid in games:
            game.finish()
            gameslock.acquire()
            del games[gid]
            gameslock.release()
        
    def getgid(s):
        peer = str(s.connection.getpeername()) + str(time.time()) + str(os.urandom(4))
        return hashlib.sha224(peer).hexdigest()[:16]
        
 
class ThreadingHTTPServer(SocketServer.ThreadingMixIn, BaseHTTPServer.HTTPServer):
    def finish_request(self, request, client_address):
        request.settimeout(60)
        BaseHTTPServer.HTTPServer.finish_request(self, request, client_address) 
 
if __name__ == '__main__':
    if len(sys.argv) < 2:
        print "Usage: python httpserver.py <ostari file>"
        sys.exit(0)
    server_class = ThreadingHTTPServer
    httpd = server_class((HOST_NAME, PORT_NUMBER), MyHandler)
    print time.asctime() + " Server Starts - %s:%s\n" % (HOST_NAME, PORT_NUMBER)
    try:
       httpd.serve_forever()
    except KeyboardInterrupt:
       pass
    httpd.server_close()
    print time.asctime() +  " Server Stops - %s:%s\n" % (HOST_NAME, PORT_NUMBER)

