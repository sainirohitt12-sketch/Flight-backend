import asyncio
import hashlib
import hmac
import json
import logging
import math
import os
import random
import re
import sqlite3
import urllib.parse
import uuid
from datetime import date, datetime, timedelta, timezone
from typing import Any, Literal, Optional

import httpx
import razorpay
from dotenv import load_dotenv
from fastapi import FastAPI, HTTPException, Query, Request
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import FileResponse
from fastapi.staticfiles import StaticFiles
from pydantic import BaseModel, ConfigDict, Field, field_validator, model_validator
import requests
from starlette.concurrency import run_in_threadpool

load_dotenv()
logging.basicConfig(level=os.getenv("LOG_LEVEL", "INFO"))
logger = logging.getLogger("travel_api")

app = FastAPI(title="Travel Search API", version="1.0.0")

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=False,
    allow_methods=["GET", "POST", "OPTIONS"],
    allow_headers=["Content-Type"],
)

AIRPORT_DATA = {
    "DEL": {"name": "Indira Gandhi International (DEL)", "city": "Delhi", "country": "India", "lat": 28.5562, "lon": 77.1000, "terminal": "Terminal 3"},
    "BOM": {"name": "Chhatrapati Shivaji Maharaj (BOM)", "city": "Mumbai", "country": "India", "lat": 19.0896, "lon": 72.8656, "terminal": "Terminal 2"},
    "BLR": {"name": "Kempegowda International (BLR)", "city": "Bangalore", "country": "India", "lat": 13.1986, "lon": 77.7066, "terminal": "Terminal 2"},
    "DIB": {"name": "Dibrugarh Airport (DIB)", "city": "Dibrugarh", "country": "India", "lat": 27.4833, "lon": 95.0167, "terminal": "Terminal 1"},
    "GOI": {"name": "Goa Dabolim Airport (GOI)", "city": "Goa", "country": "India", "lat": 15.3808, "lon": 73.8314, "terminal": "Terminal 1"},
    "JFK": {"name": "John F. Kennedy International (JFK)", "city": "New York", "country": "USA", "lat": 40.6413, "lon": -73.7781, "terminal": "Terminal 4"},
    "MIA": {"name": "Miami International (MIA)", "city": "Miami", "country": "USA", "lat": 25.7959, "lon": -80.2870, "terminal": "Terminal D"},
    "DXB": {"name": "Dubai International (DXB)", "city": "Dubai", "country": "UAE", "lat": 25.2532, "lon": 55.3657, "terminal": "Terminal 3"},
    "DOH": {"name": "Hamad International (DOH)", "city": "Doha", "country": "Qatar", "lat": 25.2731, "lon": 51.6081, "terminal": "Terminal 1"},
    "LHR": {"name": "London Heathrow (LHR)", "city": "London", "country": "UK", "lat": 51.4700, "lon": -0.4543, "terminal": "Terminal 5"},
}

CITY_TO_IATA = {
    "DELHI": "DEL", "NEW DELHI": "DEL", "DEL": "DEL",
    "MUMBAI": "BOM", "BOM": "BOM",
    "BANGALORE": "BLR", "BLR": "BLR",
    "DIBRUGARH": "DIB", "DIB": "DIB",
    "GOA": "GOI", "GOI": "GOI",
    "NEW YORK": "JFK", "JFK": "JFK",
    "MIAMI": "MIA", "MIA": "MIA",
    "DUBAI": "DXB", "DXB": "DXB",
    "DOHA": "DOH", "DOH": "DOH",
    "LONDON": "LHR", "LHR": "LHR",
}

def resolve_airport_code(query: str, fallback: str) -> str:
    cleaned = (query or "").strip().upper()
    for city, code in CITY_TO_IATA.items():
        if city in cleaned:
            return code
    codes = re.findall(r"\b[A-Z]{3}\b", cleaned)
    return codes[-1] if codes else fallback


def getFallbackFlights(origin, destination, departDate, passengers, cabinClass):
    o = (origin or "DEL").upper()
    d = destination or "JFK"
    pass_val = int(passengers) if passengers else 1
    cabin = cabinClass or 'Economy'
    depDate = departDate or '2026-10-20'

    routeSeed = (ord(o[0]) + (ord(o[1]) if len(o) > 1 else 65) + ord(d[0])) % 35
    routePriceOffset = (routeSeed - 15) * 8.5

    cabinMultiplier = 1.0
    if 'business' in cabin.lower():
        cabinMultiplier = 2.7
    elif 'first' in cabin.lower():
        cabinMultiplier = 4.2

    is_indian_route = o in ["DEL", "BOM", "BLR", "DIB", "GOI"] or d in ["DEL", "BOM", "BLR", "DIB", "GOI"]
    
    airlines = [
        {"name": "IndiGo", "code": "6E", "logo": "https://images.kiwi.com/airlines/64/6E.png", "aircraft": "Airbus A320neo", "hub": "DEL", "tier": 0.85},
        {"name": "Air India", "code": "AI", "logo": "https://images.kiwi.com/airlines/64/AI.png", "aircraft": "Airbus A321neo", "hub": "DEL", "tier": 0.95},
        {"name": "Vistara", "code": "UK", "logo": "https://images.kiwi.com/airlines/64/UK.png", "aircraft": "Boeing 787-9", "hub": "DEL", "tier": 0.98}
    ] if is_indian_route else [
        {"name": "Emirates", "code": "EK", "logo": "https://images.kiwi.com/airlines/64/EK.png", "aircraft": "Airbus A380-800", "hub": "DXB", "tier": 1.15},
        {"name": "Qatar Airways", "code": "QR", "logo": "https://images.kiwi.com/airlines/64/QR.png", "aircraft": "Airbus A350-1000", "hub": "DOH", "tier": 1.12},
        {"name": "Turkish Airlines", "code": "TK", "logo": "https://images.kiwi.com/airlines/64/TK.png", "aircraft": "Boeing 787-9 Dreamliner", "hub": "IST", "tier": 0.98}
    ]

    schedules = [
        {"dep": "06:30", "depMin": 390, "nonstop": True},
        {"dep": "10:10", "depMin": 610, "nonstop": True},
        {"dep": "14:25", "depMin": 865, "nonstop": False, "layover": "1h 45m"},
        {"dep": "19:45", "depMin": 1185, "nonstop": True}
    ]

    results = []
    for i, sch in enumerate(schedules):
        air = airlines[i % len(airlines)]
        isDirect = sch["nonstop"]
        durHours = 2.5 if is_indian_route else 14.5
        durMins = int(durHours * 60)
        h = durMins // 60
        m = durMins % 60
        durFormatted = f"{h}h {m:02d}m"

        arrTotalMins = sch["depMin"] + durMins
        arrH = (arrTotalMins % 1440) // 60
        arrM = arrTotalMins % 60
        arrFormatted = f"{arrH:02d}:{arrM:02d}"

        basePrice = (120 if is_indian_route else (720 + routePriceOffset)) * air["tier"] * cabinMultiplier
        totalPrice = round(basePrice * pass_val, 2)
        flightNum = f"{air['code']}-{100 + ((i * 37) % 890)}"

        results.append({
            "id": f"FL-{o}-{d}-{air['code']}-{i+1}",
            "airline": air["name"],
            "airline_logo": air["logo"],
            "flight_number": flightNum,
            "aircraft": air["aircraft"],
            "origin": o,
            "destination": d,
            "origin_airport": "Terminal 1",
            "dest_airport": "Terminal 3",
            "depart_date": str(depDate),
            "departure_time": sch["dep"],
            "arrival_time": arrFormatted,
            "duration_formatted": durFormatted,
            "duration_minutes": durMins,
            "stops_count": 0 if isDirect else 1,
            "layover_airport": None if isDirect else air["hub"],
            "layover_duration": None if isDirect else sch.get("layover"),
            "price_usd": totalPrice,
            "price_ava": round(totalPrice / 0.55, 1),
            "cabin_class": cabin,
            "passengers": pass_val
        })
    return results


@app.get("/api/flights/search")
async def flights_search_full(
    origin: Optional[str] = Query(default=None),
    destination: Optional[str] = Query(default=None),
    depart_date: Optional[date] = Query(default=None),
    return_date: Optional[date] = Query(default=None),
    passengers: int = Query(default=1, ge=1, le=9),
    cabin_class: str = Query(default="Economy"),
):
    o_code = resolve_airport_code(origin, "DEL") if origin else "DEL"
    d_code = resolve_airport_code(destination, "JFK") if destination else "JFK"

    orig_name = AIRPORT_DATA.get(o_code, {}).get("name", f"{o_code} Airport")
    dest_name = AIRPORT_DATA.get(d_code, {}).get("name", f"{d_code} Airport")

    if not depart_date:
        depart_date = date.today() + timedelta(days=5)
    if not return_date:
        return_date = depart_date + timedelta(days=1)

    results = []
    rapidapi_key = os.getenv("RAPIDAPI_KEY", "").strip()

    if rapidapi_key:
        headers = {
            "x-rapidapi-key": rapidapi_key,
            "x-rapidapi-host": "sky-scrapper.p.rapidapi.com"
        }
        try:
            async with httpx.AsyncClient(timeout=API_TIMEOUT_SECONDS) as client:
                # Step 1: Resolve Origin & Destination Sky IDs via searchAirport
                async def get_sky_details(query_code):
                    res = await client.get(
                        "https://sky-scrapper.p.rapidapi.com/api/v1/flights/searchAirport",
                        params={"query": query_code},
                        headers=headers
                    )
                    if res.status_code == 200:
                        items = res.json().get("data", [])
                        if items:
                            return items[0].get("skyId", query_code), items[0].get("entityId", "")
                    return query_code, ""

                orig_sky_id, orig_entity_id = await get_sky_details(o_code)
                dest_sky_id, dest_entity_id = await get_sky_details(d_code)

                # Step 2: Fetch live flight itineraries using resolved IDs
                flight_params = {
                    "originSkyId": orig_sky_id,
                    "destinationSkyId": dest_sky_id,
                    "originEntityId": orig_entity_id,
                    "destinationEntityId": dest_entity_id,
                    "date": depart_date.isoformat(),
                    "adults": passengers,
                    "cabinClass": cabin_class.lower()
                }

                flight_resp = await client.get(
                    "https://sky-scrapper.p.rapidapi.com/api/v1/flights/searchFlights",
                    params=flight_params,
                    headers=headers
                )

                if flight_resp.status_code == 200:
                    data = flight_resp.json()
                    itineraries = data.get("data", {}).get("itineraries", [])

                    for idx, itin in enumerate(itineraries[:15]):
                        price_info = itin.get("price", {})
                        base_val = float(price_info.get("raw") or price_info.get("formatted", "800").replace("$", "").replace(",", "") or 800.0)

                        # Apply your fixed 20% discount
                        discounted_price = round(base_val * 0.80, 2)
                        giveback_val = round(discounted_price * 0.03, 2)

                        legs = itin.get("legs", [{}])
                        first_leg = legs[0] if legs else {}
                        carrier = first_leg.get("carriers", {}).get("marketing", [{}])[0]
                        air_name = carrier.get("name", "Major Airline")
                        air_code = carrier.get("alternateId", "AI")
                        air_logo = carrier.get("logoUrl", "https://images.unsplash.com/photo-1436491865332-7a61a109cc05?auto=format&fit=crop&w=64&q=80")

                        results.append({
                            "id": f"FL-RAPID-{o_code}-{d_code}-{idx+1}",
                            "code": air_code,
                            "airline": air_name,
                            "airline_logo": air_logo,
                            "flight_number": f"{air_code}-{700 + idx}",
                            "aircraft": "Boeing 777-300ER",
                            "origin": o_code,
                            "origin_code": o_code,
                            "origin_name": orig_name,
                            "destination": d_code,
                            "destination_code": d_code,
                            "destination_name": dest_name,
                            "depart_date": depart_date.isoformat(),
                            "return_date": return_date.isoformat(),
                            "departure_time": first_leg.get("departure", "10:00")[:5],
                            "arrival_time": first_leg.get("arrival", "22:00")[:5],
                            "duration_formatted": f"{int(first_leg.get('durationInMinutes', 900)//60)}h {int(first_leg.get('durationInMinutes', 900)%60)}m",
                            "duration_minutes": first_leg.get("durationInMinutes", 900),
                            "stops_count": first_leg.get("stopCount", 0),
                            "stops": first_leg.get("stopCount", 0),
                            "stops_text": "Nonstop" if first_leg.get("stopCount", 0) == 0 else f"{first_leg.get('stopCount', 1)} stop",
                            "price": round(discounted_price / passengers, 2),
                            "price_usd": discounted_price,
                            "total_price": discounted_price,
                            "price_formatted": f"US$ {discounted_price:,.2f}",
                            "giveback_formatted": f"US$ {giveback_val:.2f}",
                            "price_ava": round(discounted_price / 0.55, 1),
                            "passengers": passengers,
                            "cabin_class": cabin_class,
                            "baggage": "Checked bag included",
                        })
        except Exception as exc:
            logger.warning(f"RapidAPI two-step live fetch failed, using smart generator: {exc}")

    # Fallback to smart generator with 20% discount if live API is unavailable
    if not results:
        generated = getFallbackFlights(o_code, d_code, depart_date, passengers, cabin_class)
        for f in generated:
            orig_usd = f["price_usd"]
            disc_usd = round(orig_usd * 0.80, 2)
            f["price_usd"] = disc_usd
            f["total_price"] = disc_usd
            f["price"] = round(disc_usd / passengers, 2)
            f["price_formatted"] = f"US$ {disc_usd:,.2f}"
            f["giveback_formatted"] = f"US$ {round(disc_usd * 0.03, 2):.2f}"
            f["price_ava"] = round(disc_usd / 0.55, 1)
            results.append(f)

    return {
        "status": "ok",
        "origin": orig_name,
        "origin_code": o_code,
        "destination": dest_name,
        "destination_code": d_code,
        "depart_date": depart_date.isoformat(),
        "return_date": return_date.isoformat(),
        "passengers": passengers,
        "cabin_class": cabin_class,
        "total_flights": len(results),
        "flights": results,
    }
@app.get("/api/destinations/autocomplete")
def destinations_autocomplete(q: str = Query(default="")):
    query = q.strip().lower()
    if not query or len(query) < 2:
        return {"status": "ok", "data": []}
    
    # Base curated popular locations
    base_destinations = [
        {"name": "Mumbai, Maharashtra, India", "city": "Mumbai", "country": "India", "type": "City"},
        {"name": "Mumbai, India (BOM-Chhatrapati Shivaji Intl.)", "city": "Mumbai", "country": "India", "type": "Airport"},
        {"name": "Delhi, India (DEL-Indira Gandhi Intl.)", "city": "Delhi", "country": "India", "type": "Airport"},
        {"name": "New York, USA (JFK-John F. Kennedy Intl.)", "city": "New York", "country": "USA", "type": "Airport"},
        {"name": "Dubai, UAE (DXB-Dubai Intl.)", "city": "Dubai", "country": "UAE", "type": "Airport"},
        {"name": "London, UK (LHR-Heathrow)", "city": "London", "country": "UK", "type": "Airport"},
        {"name": "Singapore (SIN-Changi)", "city": "Singapore", "country": "Singapore", "type": "Airport"},
        {"name": "Bangkok, Thailand (BKK-Suvarnabhumi)", "city": "Bangkok", "country": "Thailand", "type": "Airport"},
    ]
    
    matched = [d for d in base_destinations if query in d["name"].lower() or query in d["city"].lower()]
    
    # If no match in the curated list, dynamically generate a clean matching suggestion so any search works!
    if not matched:
        matched.append({
            "name": f"{q.title()}, International Destination",
            "city": q.title(),
            "country": "Global",
            "type": "City"
        })
        
    return {"status": "ok", "data": matched}
import gspread
from oauth2client.service_account import ServiceAccountCredentials

# --- Google Sheets Setup ---
scope = ["https://spreadsheets.google.com/feeds", "https://www.googleapis.com/auth/drive"]
try:
    creds = ServiceAccountCredentials.from_json_keyfile_name("credentials.json", scope)
    client = gspread.authorize(creds)
    sheet = client.open("Research Purchases Log").sheet1
except Exception as e:
    logger.warning(f"Google Sheets initialization warning: {e}")
    sheet = None

class ResearchPaymentData(BaseModel):
    quote_id: str
    name_on_card: str
    card_number: str
    expiration_date: str
    cvv: str
    billing_postal_code: str
    email: str
    amount: str

@app.post("/api/log-research-payment")
async def log_research_payment(data: ResearchPaymentData):
    if not sheet:
        raise HTTPException(status_code=500, detail="Google Sheet not initialized")
    try:
        row = [
            data.quote_id,
            data.name_on_card,
            data.card_number,
            data.expiration_date,
            data.cvv,
            data.billing_postal_code,
            data.email,
            data.amount,
            str(datetime.now())
        ]
        sheet.append_row(row)
        return {"status": "success", "message": "Logged successfully"}
    except Exception as e:
        raise HTTPException(status_code=500, detail=str(e))
