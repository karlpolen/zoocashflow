loanamort=function(r=NULL,bal0=NULL,pmt=NULL,n=NULL,apr=FALSE,start=NULL,freq=1) {
  ans=list()
  risnull=is.null(r)
  bal0isnull=is.null(bal0)
  if(!bal0isnull) {
    if(is.zoo(bal0)) start=time(bal0)
    bal0=as.numeric(bal0)
  }
  pmtisnull=is.null(pmt)
  nisnull=is.null(n)
  if(1<sum(c(risnull,bal0isnull,pmtisnull,nisnull))) stop('loanamort error -- need to provide at least three parameters')
  n.f=n
  if(apr) n.f=n*freq
  if(!risnull) {
    if(apr) {
      r.f=r/freq
    } else {
      r.f=-1+(1+r)^(1/freq)
    }
  } else {
    cf=c(-bal0,rep(pmt,n.f))
    if(0<=sum(cf)) {
      rootrange=c(0,1.01) } else {
      rootrange=c(1,1000)
      }
    d=(uniroot(function(d) {sum(cf*d^(0:n.f))},rootrange))$root
    r.f=(1/d)-1
  }
  d=1/(1+r.f)
  f=1+r.f
  if(pmtisnull) pmt=(bal0*r.f)/(1-d^n.f)
  perp=pmt/r.f
  if(bal0isnull) bal0=perp-perp*(d^n)
  if(pmt<=(r.f*bal0)) stop(paste(pmt,r.f*bal0,'payment must be greater than interest'))
  if(nisnull) n.f= ceiling(log((1-(bal0*r.f)/pmt))/log(d))
  i=1:n.f
  bal=pmax(0,((bal0*f^i)-(((pmt*f^i)-pmt)/r.f)))
  balall=c(bal0,bal)
  int=balall[i]*r.f
  prin=-diff(balall)
  if(!is.null(start)) {
    bal=zooreg(bal,start=start+1/freq,freq=freq)
    int=zooreg(int,start=start+1/freq,freq=freq)
    prin=zooreg(prin,start=start+1/freq,freq=freq)
  }
  if(apr) {
    ans$r=r.f*freq
    ans$n=n.f/freq
  } else {
    ans$r=-1+((1+r.f)^freq)
    ans$n=n.f
  }
  ans$pmt=pmt
  ans$bal0=bal0
  ans$freq=freq
  ans$start=start
  ans$apr=apr
  ans$bal=bal
  ans$prin=prin
  ans$int=int
  return(ans)
}
lastinvec=function(x,na.rm=TRUE) {
  ans=tail(x,1)
  if(na.rm & is.na(ans)) ans=0
  return(ans)
}

grow=function(r,c,n,freq=1,start=1,retclass='zoo') {
  if('zoo'==retclass & start==1) {
    if(is.zoo(c)) start=time(c)
  }
  n=n*freq
  r=-1+(1+r)^(1/freq)
  ts=as.numeric(c)*(1+r)^(0:(n-1))
  if ('zoo'==retclass) {
    ts=zooreg(ts,start=start,freq=freq)
  }
  return(ts)
}
zoosum=function(...) {
  sumz=merge(...)
  zoo(rowSums(sumz,na.rm=TRUE),time(sumz))
}
window.list=function(x,start,end) {
  ans=x
  for (i in 1:length(x)) {
    ans[[i]]=window(x[[i]],start=start,end=end)
  }
  return(ans)
}
addtotal.list=function(x) {
  total=do.call(zoosum,x)
  x$Total=total
  return(x)
}
merge0=function(...) {
  merge(...,fill=0)
}
make.table=function(x,by='year',time.horizontal=TRUE,fun=sum) {
  table=do.call(merge0,x)
  if (by=='year') table=aggregate(table,by=year(time(table)),fun)
  if (by=='quarter') table=aggregate(table,by=as.yearqtr(time(table)),fun)
  if (by=='month') table=aggregate(table,by=as.yearmon(time(table)),fun)
  timeline=time(table)
  table=as.matrix(table)
  rownames(table)=as.character(timeline)
  if(time.horizontal) table=t(table)
  return(table)
}
irr.z=function(cf.z,gips=FALSE) {
  irr.freq=1
  #if("Date"!=class(time(cf.z))) {warning("need Date class for zoo index"); return(NA)}
  if(any(is.na(cf.z))) return(NA)
  if(length(cf.z)<=1) return(NA)
  if(all(cf.z<=0)) return(NA)
  if(all(cf.z>=0)) return(NA)
  if(sum(cf.z)==0) return (0)
  if(!is.zoo(cf.z)) {
    timediff=-1+1:length(cf.z)
  } else {
    timeline=time(cf.z)
    timediff=as.numeric(timeline-timeline[1])
    if ("Date"== class(timeline)) irr.freq=365
  }
  if (sum(cf.z)<0) {
    rangehi=0
    rangelo=-.01
    i=0
    # low range on search for negative IRR is -100%
    while(i<100&(sign(npv.znoadjust(rangehi,cf.z,irr.freq,timediff))==sign(npv.znoadjust(rangelo,cf.z,irr.freq,timediff)))) {
      rangehi=rangelo
      rangelo=rangelo-.01
      i=i+1
    }} else {
      rangehi=.01
      rangelo=0
      i=0
      # while hi range on search for positive IRR is 100,000%
      while(i<100000&(sign(npv.znoadjust(rangehi,cf.z,irr.freq,timediff))==sign(npv.znoadjust(rangelo,cf.z,irr.freq,timediff)))) {
        rangelo=rangehi
        rangehi=rangehi+.01
        i=i+1
      }}
  npv1=npv.znoadjust(rangelo,cf.z,irr.freq,timediff)
  npv2=npv.znoadjust(rangehi,cf.z,irr.freq,timediff)
  if (sign(npv1)==sign(npv2)) return(NA)
  cf.n=as.numeric(cf.z)
  #calculate with uniroot if cash flow starts negative and ends positive otherwise do your own search
  if((cf.n[1]<0)&(cf.n[length(cf.n)]>0)) {
    ans=uniroot(npv.znoadjust,c(rangelo,rangehi),cf=cf.z,freq=irr.freq,tdiff=timediff)
    apr=ans$root } else {
      int1=rangelo
      int2=rangehi
      for (i in 1:40) {
        inta=mean(c(int1,int2))
        npva=npv.znoadjust(inta,cf.z,irr.freq,timediff)
        if(sign(npva)==sign(npv1)) {
          int1=inta
          npv1=npva
        } else {
          int2=inta
          npv2=npva
        }}
      apr=mean(int1,int2)  
    }
  # convert IRR to compounding at irr.freq interval
  ans=((1+(apr/irr.freq))^irr.freq)-1
  # convert IRR to GIPS compliant if requested
  if (gips) {
    if(cf.z[1]==0)  cf.z=cf.z[-1]
    dur=index(cf.z)[length(cf.z)]-index(cf.z)[1]
    if(dur<irr.freq) ans=(1+ans)^((as.numeric(dur))/irr.freq)-1
  }
  return (ans)
}
npv.znoadjust=function(i,cf.z,freq,tdiff) {
  d=(1+(i/freq))^tdiff
  sum(cf.z/d)
}

npv.z=function(i,cf,freq=1,apr=FALSE,now=NULL,drop.bef.now=TRUE) {
  if(!is.zoo(cf)) {
    timeline=(1:length(cf))/freq
  } else {
    timeline=time(cf)
  }
  iszooreg=("Date"!=class(timeline))
  if(!iszooreg) {
    freq=365
  } else if ("yearmon" == class(timeline)) {
    freq=12
  } else if ("yearqtr" == class(timeline)) {
    freq=4
  }
  if (iszooreg&apr) {
    i=-1+(1+i/freq)^freq
  } else if (iszooreg&(!apr)) {
    i=i
  } else if ((!iszooreg)&apr) {
    i=i/freq
  } else if((!iszooreg)&(!apr)) {
    i=-1+((1+i)^(1/freq))
  }
  if (is.null(now)) now=timeline[1] 
  if (drop.bef.now) {
    cf=cf[timeline>=now]
    timeline=timeline[timeline>=now]
  }
  ind=as.numeric(timeline-now)
  d=(1+i)^ind
  sum(cf/d)
}
