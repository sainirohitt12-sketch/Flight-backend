import os
import httpx
from fastapi import FastAPI, HTTPException
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel

app = FastAPI()

# Enable CORS so your static Hostinger frontend can talk to this backend
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],  # In production, replace with your actual domain (e.g., https://traalaa.com)
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

TRAVELPAYOUTS_API_TOKEN = os.getenv("533eea91abf952fbe89c0b3768fa2112", "")
NOWPAYMENTS_API_KEY = os.getenv("6GKAJAJ-B9E4WC0-NMJPMVA-K7FJJCH", "")

class BookingRequest(BaseModel):
    flight_number: str
    price: float
    currency: str = "USD"
    pay_currency: str = "USDT" # crypto user wants to pay with

@app.get("/api/search-flights")
async def search_flights(origin: str, destination: str, depart_date: str):
    url = "https://api.travelpayouts.com/v1/prices/cheap"
    params = {
        "origin": origin.upper(),
        "destination": destination.upper(),
        "depart_date": depart_date
    }
    headers = {
        "x-access-token": TRAVELPAYOUTS_API_TOKEN
    }
    
    async with httpx.AsyncClient() as client:
        response = await client.get(url, params=params, headers=headers)
        
    if response.status_code != 200:
        raise HTTPException(status_code=response.status_code, detail="Error fetching flights from Travelpayouts")
        
    return response.json()

@app.post("/api/create-crypto-invoice")
async def create_crypto_invoice(data: BookingRequest):
    # Integrate with NOWPayments API to generate a crypto payment invoice
    url = "https://api.nowpayments.io/v1/invoice"
    headers = {
        "x-api-key": NOWPAYMENTS_API_KEY,
        "Content-Type": "application/json"
    }
    payload = {
        "price_amount": data.price,
        "price_currency": data.currency.lower(),
        "pay_currency": data.pay_currency.lower(),
        "order_id": f"FLIGHT-{data.flight_number}",
        "order_description": f"Flight Ticket #{data.flight_number}",
        "success_url": "https://traalaa.com/booking-success",
        "cancel_url": "https://traalaa.com/booking-cancelled"
    }
    
    async with httpx.AsyncClient() as client:
        response = await client.post(url, json=payload, headers=headers)
        
    if response.status_code != 201:
        raise HTTPException(status_code=response.status_code, detail="Error generating crypto invoice")
        
    return response.json()

if __name__ == "__main__":
    import uvicorn
    port = int(os.environ.get("PORT", 8080))
    uvicorn.run("main:app", host="0.0.0.0", port=port)
