import subprocess
import os
import sys
import time
import random
import threading
import argparse
import math

ITERATIONS = 100
WORKERS = 10

def parse_output(output):
    lines = map(lambda s: s.strip(), filter(None, output.split("\n")))
    result = {}
    resultmode = False
    cardsmode = False
    wws = []
    for l in lines:
        if l == "WerewolfCards":
            cardsmode = True
        elif cardsmode:
            if len(l) == 1:
                wws.append(l)
        if l == "Result":
            cardsmode = False
            resultmode = True
        elif resultmode:
            items = l.split()
            if len(items) == 2:
                result[items[0].strip(":")] = items[1]
    return result, wws
    
players = ["a", "b", "c", "d", "e"]
    
def resolve_template(template, fname, cards, ais, turns, cert, death="die"):
    f = open(template, "r")
    content = f.read()
    f.close()
    for p in players:
        content = content.replace("$card"+p, cards[p])
        content = content.replace("$ai"+p, ais[p])
    content = content.replace("$turns", str(turns))
    content = content.replace("$cert", str(cert))
    content = content.replace("$death", death)
    f = open(fname, "w")
    f.write(content)
    f.close()
    
def determine_winners(cards, result, wws):
    if not wws:
        return determine_from_cards(cards, result)
    killedww = False
    wwps = []
    nonwws = []
    for r in result:
        if result[r] == "True":
            if r in wws:
                killedww = True
        if r in wws:
            wwps.append(r)
        else:
            nonwws.append(r)
    
    if killedww:
        return nonwws
    return wwps

def determine_from_cards(cards, result):
    killedww = False
    wws = []
    nonwws = []
    for r in result:
        if result[r] == "True":
            if cards[r].startswith("Werewolf"):
                killedww = True
        if cards[r].startswith("Werewolf"):
            wws.append(r)
        else:
            nonwws.append(r)
    
    if killedww:
        return nonwws
    return wws

def rungame(id, template, cards, ais, turns, n=None, alpha=None, verbose=False):
    
    fname = id
    
    args = ["rungameA"]
    if n:
        args = args + ["-n", str(n)]
    if alpha:
        args = args + ["-a", str(alpha)]
    args = args + [fname]
    t = time.time()
    try:
        
        out = subprocess.check_output(args, stderr=subprocess.STDOUT)
    except Exception as e:
        print e.output
        return ([],0)
    result, wws = parse_output(out)
    t1 = time.time()
    if verbose:
        print result, t1 - t
    winners = determine_winners(cards, result, wws)
    if verbose:
        print winners
    return winners, t1-t
    
def threadone(stats, lock, sema, id, template, cards, ais, turns, n=None, alpha=None, verbose=False):
    winners, t = rungame(id, template, cards, ais, turns, n, alpha, verbose)
    lock.acquire()
    for w in winners:
        if w not in stats:
            stats[w] = 0
        stats[w] += 1
    stats["time"] += t
    lock.release()
    sema.release()
    
def runmany(prefix, template, cards, ais, turns, n=None, alpha=None, verbose=False, cert=0.7, death="die", iterations=ITERATIONS, workers=WORKERS):
    sema = threading.BoundedSemaphore(value=workers)
    lock = threading.Lock()
    stats = {"time": 0}
    fname = os.path.join("games", "game%s"%(prefix)+".cfg")
    resolve_template(template, fname, cards, ais, turns, cert, death)
    for i in xrange(iterations):
        sema.acquire()
        if i > 0 and (i+1)%10 == 0:
            print >>sys.stderr, i+1, "(%.2f)"%(stats.get("a", 0)*1.0/(i+1)),
        t = threading.Thread(target=threadone, args=(stats, lock, sema, fname, template, cards, ais, turns, n, alpha, verbose))
        t.start()
    time.sleep(5)
    for i in xrange(workers):
        sema.acquire()
    print >>sys.stderr, "\n"
    for s in stats:
        stats[s] = stats[s]*1.0/iterations
    return stats



    

def clean(l):
    if type(l) == list:
        return map(lambda s: s.strip(), l)
    return l.strip()
        
def make_arg_list(spec, conv=int):
    if spec is None:
        return None
    if "," in spec:
        return map(conv, clean(spec.split(",")))
    if ":" in spec:
        items = spec.split(":")
        if len(items) == 2:
            return range(int(items[0]), int(items[1]))
        start = conv(items[0])
        end = conv(items[1])
        delta = conv(items[2])
        result = []
        while start < end:
            result.append(start)
            start += delta
        result.append(end)
        return result
    return conv(spec)

gid = 0

def main(template, acard, bcard, ccard, dcard, ecard, aai, bai, cai, dai, eai, comm=[0.5,1,2], certainty=0.7, states=50, votes="m", n=25, threads=4, preset=None):
    if not os.path.exists("games"):
        os.makedirs("games")
    global gid 
    
    if type(preset) == list:
        for p in preset:
            main(template, acard, bcard, ccard, dcard, ecard, aai, bai, cai, dai, eai, comm, certainty, states, votes, n, threads, p)
        return 
    
    if preset == "commitment":
        if acard is None: 
            acard = "Werewolf1"
        if bcard is None:
            bcard = "Troublemaker"
        if ccard is None:
            ccard = "Villager1"
        if dcard is None:
            dcard = "Seer"
        if ecard is None:
            ecard = "Insomniac"
        if aai is None:
            aai = "balanced"
        if bai is None:
            bai = "capricious"
        if cai is None:
            cai = "capricious"
        if dai is None:
            dai = "capricious"
        if eai is None:
            eai = "capricious"
        if comm is None:
            comm = [0.2,0.5,0.75,1,1.5,2,5,10]
        if certainty is None:
            certainty = 0.7
        if states is None:
            states = 50
        if votes is None:
            votes = "m"
    
    if preset == "commitmentr":
        if acard is None: 
            acard = "Werewolf1"
        if bcard is None:
            bcard = "Troublemaker"
        if ccard is None:
            ccard = "Villager1"
        if dcard is None:
            dcard = "Seer"
        if ecard is None:
            ecard = "Insomniac"
        if aai is None:
            aai = "balanced"
        if bai is None:
            bai = "random"
        if cai is None:
            cai = "random"
        if dai is None:
            dai = "random"
        if eai is None:
            eai = "random"
        if comm is None:
            comm = [0.2,0.5,0.75,1,1.5,2,5,10]
        if certainty is None:
            certainty = 0.7
        if states is None:
            states = 50
        if votes is None:
            votes = "m"
            
    if preset == "states":
        if acard is None: 
            acard = "Werewolf1"
        if bcard is None:
            bcard = "Villager1"
        if ccard is None:
            ccard = "Troublemaker"
        if dcard is None:
            dcard = "Seer"
        if ecard is None:
            ecard = "Insomniac"
        if aai is None:
            aai = "balanced"
        if bai is None:
            bai = "capricious"
        if cai is None:
            cai = "capricious"
        if dai is None:
            dai = "capricious"
        if eai is None:
            eai = "capricious"
        if comm is None:
            comm = 1
        if certainty is None:
            certainty = 0.7
        if states is None:
            states = [1,3,5,10,20, 25, 50, 100, 150, 200, 500]
        if votes is None:
            votes = "m"
            
    if preset == "lopsided":
        if acard is None: 
            acard = "Werewolf1"
        if bcard is None:
            bcard = "Troublemaker"
        if ccard is None:
            ccard = "Insomniac"
        if dcard is None:
            dcard = "Seer"
        if ecard is None:
            ecard = "Robber"
        if aai is None:
            aai = "balanced"
        if bai is None:
            bai = "capricious"
        if cai is None:
            cai = "capricious"
        if dai is None:
            dai = "capricious"
        if eai is None:
            eai = "capricious"
        if comm is None:
            comm = [0.2, 0.5, 0.7, 1, 1.5, 2]
        if certainty is None:
            certainty = 0.7
        if states is None:
            states = 50
        if votes is None:
            votes = "m"
            
    if preset == "suspicious":
        if acard is None: 
            acard = "Werewolf1"
        if bcard is None:
            bcard = "Troublemaker"
        if ccard is None:
            ccard = "Insomniac"
        if dcard is None:
            dcard = "Seer"
        if ecard is None:
            ecard = "Robber"
        if aai is None:
            aai = "balanced"
        if bai is None:
            bai = "capricious"
        if cai is None:
            cai = "capricious"
        if dai is None:
            dai = "capricious"
        if eai is None:
            eai = "capricious"
        if comm is None:
            comm = [0.5, 1, 1.5]
        if certainty is None:
            certainty = [0.4, 0.5, 0.6, 0.7, 0.8]
        if states is None:
            states = 50
        if votes is None:
            votes = "m"
        
    if acard is None: 
        acard = "Werewolf1"
    if bcard is None:
        bcard = "Troublemaker"
    if ccard is None:
        ccard = "Villager1"
    if dcard is None:
        dcard = "Seer"
    if ecard is None:
        ecard = "Insomniac"
    if aai is None:
        aai = "balanced"
    if bai is None:
        bai = "random"
    if cai is None:
        cai = "random"
    if dai is None:
        dai = "random"
    if eai is None:
        eai = "random"
    if comm is None:
        comm = [0.5,1,2]
    if certainty is None:
        certainty = 0.7
    if states is None:
        states = 50
    if votes is None:
        votes = "m"
    if threads is None:
        threads = 4
    if n is None:
        n = 25

    if type(comm) == list:
        for c in comm:
            main(template, acard, bcard, ccard, dcard, ecard, aai, bai, cai, dai, eai, c, certainty, states, votes, n, threads)
        return
    if type(certainty) == list:
        for c in certainty:
            main(template, acard, bcard, ccard, dcard, ecard, aai, bai, cai, dai, eai, comm, c, states, votes, n, threads)
        return
    if type(states) == list:
        for c in states:
            main(template, acard, bcard, ccard, dcard, ecard, aai, bai, cai, dai, eai, comm, certainty, c, votes, n, threads)
        return
    if type(votes) == list:
        for c in votes:
            main(template, acard, bcard, ccard, dcard, ecard, aai, bai, cai, dai, eai, comm, certainty, states, c, n, threads)
        return
        
    def toai(ai, comm):
        if ai == "balanced":
            return "balanced(%.2f)"%(comm)
        return ai
    
    death = "die"
    if votes.startswith("p"):
        death = "die,die2"
    
    cards = {"a": acard, "b": bcard, "c": ccard, "d": dcard, "e": ecard}
    ais = {"a": toai(aai, comm), "b": toai(bai, comm), "c": toai(cai, comm), "d": toai(dai, comm), "e": toai(eai, comm)}
    
    print "setup:", cards, ais
    print "certainty:", certainty, "votes:", votes
    print "states:", states
    print "running", n, "games, 95% confidence interval: +/-", 100*1.96*math.sqrt(0.5*0.5/n), "%"
    print "input file: games/game%d.cfg"%gid, "starting", threads, "threads"
    stats = runmany("%d"%gid, template, cards, ais, 7, n=states, cert=certainty, death=death, iterations=n, workers=threads)
    gid += 1
    r1 = stats.get("a", 0)*100
    print "player A won", r1, "%"
    print " ", stats
    print "\n\n\n"   

wws = 0
villagers = 0

def fixrole(role):
    global wws, villagers
    if role == "Rascal":
        return "Troublemaker"
    if role == "Werewolf":
        wws += 1
        return role + str(wws)
    if role == "Villager":
        villagers += 1
        return role + str(villagers)
    return role

   
if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Run a number of One Night Ultimate Werewolf Games.')
    parser.add_argument('template', help='Which template file to use')
    parser.add_argument('-n', dest='n', default=20,
                        help='How many games to run for each parameter combination (default: 20)')     
    parser.add_argument('-t', '--threads', dest='threads', default=4,
                        help='How many threads/games to run in parallel. It is recommended to choose at most as many as you have CPUs (default: 4)')
    parser.add_argument('-a', '--a-card', dest="arole", default=None, help="Which role card player A starts with (default: Werewolf1)")
    parser.add_argument('-b', '--b-card', dest="brole", default=None, help="Which role card player B starts with (default: Troublemaker)")
    parser.add_argument('-c', '--c-card', dest="crole", default=None, help="Which role card player C starts with (default: Villager1)")
    parser.add_argument('-d', '--d-card', dest="drole", default=None, help="Which role card player D starts with (default: Seer)")
    parser.add_argument('-e', '--e-card', dest="erole", default=None, help="Which role card player E starts with (default: Insomniac)")
    
    parser.add_argument('-1', '--a-ai', dest="aai", default=None, help="Which agent type player A uses (default: balanced)")
    parser.add_argument('-2', '--b-ai', dest="bai", default=None, help="Which agent type player B uses (default: random)")
    parser.add_argument('-3', '--c-ai', dest="cai", default=None, help="Which agent type player C uses (default: random)")
    parser.add_argument('-4', '--d-ai', dest="dai", default=None, help="Which agent type player D uses (default: random)")
    parser.add_argument('-5', '--e-ai', dest="eai", default=None, help="Which agent type player E uses (default: random)")
    
    parser.add_argument('-o', '--commitment', dest='commitment', default=None, help='The level of commitment for all balanced agents (default: 0.5,1,2)')
    parser.add_argument('-r', '--certainty', dest='certainty', default=None, help='The level of certainty required for an agent in a belief in order to adopt a certain goal (default: 0.7)')
    parser.add_argument('-s', '--states', dest='states', default=None, help='The number of states expanded during the planning process (default: 50)')
    parser.add_argument('-v', '--votes', dest='votes', default=None, help='Whether agents need a majority (m) or just a plurality (p) of votes to be voted off (default: m)')
                        
    parser.add_argument("-p", "--preset", dest="preset", default=None, help="Which one of the preset game setups to use; individual values can be overridden by use of the appropriate command line options")
    
    args = parser.parse_args()
    main(args.template, fixrole(args.arole), fixrole(args.brole), fixrole(args.crole), fixrole(args.drole), fixrole(args.erole), args.aai, args.bai, args.cai, args.dai, args.eai, 
         make_arg_list(args.commitment, float), make_arg_list(args.certainty, float), make_arg_list(args.states), make_arg_list(args.votes, str), args.n, args.threads, make_arg_list(args.preset, str))